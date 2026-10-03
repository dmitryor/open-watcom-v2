/****************************************************************************
*
*                            Open Watcom Project
*
*  ========================================================================
*
*    This file is distributed under the Sybase Open Watcom Public License.
*
*  ========================================================================
*
* Description:  Register selection by integer programming (retal-c
*               experiment, after Appel and George's optimal spilling).
*
*   The allocator gives each conflict (a live range) a register or a memory
*   home for its whole life, greedily in order of estimated savings. Here,
*   once per procedure before the first sort, an integer program chooses
*   which conflicts to keep in registers:
*
*       maximise    sum over conflicts c of  savings(c) * x(c)
*       subject to  for every instruction i and register class K,
*                   sum over c live at i that can only use K of
*                   words(c) * x(c) <= free registers of K at i
*                   x(c) in {0, 1}
*
*   The classes are the word registers, the index registers (BX SI DI BP),
*   the byte-addressable ones (AX BX CX DX) and ES; free means not held by a
*   precoloured register live there, and for conflicts live across the
*   instruction not clobbered by it either. These are necessary conditions
*   for an assignment, not sufficient ones, so the result only orders the
*   allocation: the chosen conflicts are allocated first, by their original
*   savings, and the rest after them as before, so any register left free
*   still goes to someone.
*
*   The program is written to a file and solved by an external command,
*   WCG_ILP_SOLVER (given the problem and solution paths), unless every
*   conflict fits anyway. WCG_ILP=greedy keeps the greedy order and only
*   changes the weights; WCG_ILP_WEIGHTS=loop prices savings with 10 per
*   loop level instead of the -os/-ot weights; WCG_ILP_DEBUG traces.
*
****************************************************************************/


#include "_cgstd.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include "coderep.h"
#include "data.h"
#include "cgmem.h"
#include "rgtbl.h"
#include "savings.h"
#include "regsave.h"
#include "feprotos.h"
#include "ilpsel.h"


#define NWORD           7       /* AX BX CX DX SI DI BP */
#define BIT_ES          0x80
#define CLS_WORD        0x7F
#define CLS_INDEX       0x72    /* BX SI DI BP */
#define CLS_BYTE        0x0F    /* AX BX CX DX */
#define CHOSEN_BASE     0x40000000UL

typedef struct {
    conflict_node   *conf;
    unsigned        mask;
    int             words;
    save_def        obj;
    save_def        orig;
} cand;

static  hw_reg_set      Word[NWORD];
static  label_handle    DoneLabel;     /* procedure already selected (CurrProc is reused) */
static  int             Calls;


static  void    InitWords( void )
/*******************************/
{
    Word[0] = HW_AX;
    Word[1] = HW_BX;
    Word[2] = HW_CX;
    Word[3] = HW_DX;
    Word[4] = HW_SI;
    Word[5] = HW_DI;
    Word[6] = HW_BP;
}


static  unsigned    RegMask( hw_reg_set regs )
/********************************************/
{
    unsigned    mask;
    int         r;

    mask = 0;
    for( r = 0; r < NWORD; ++r ) {
        if( HW_Ovlap( regs, Word[r] ) ) {
            mask |= 1U << r;
        }
    }
    if( HW_Ovlap( regs, HW_ES ) )
        mask |= BIT_ES;
    return( mask );
}


static  unsigned    PossibleMask( conflict_node *conf )
/*****************************************************/
{
    const hw_reg_set    *set;
    hw_reg_set          all;

    if( conf->possible >= RL_NUMBER_OF_SETS )
        return( CLS_WORD );
    HW_CAsgn( all, HW_EMPTY );
    for( set = RegSets[conf->possible]; !HW_CEqual( *set, HW_EMPTY ); ++set ) {
        HW_TurnOn( all, *set );
    }
    return( RegMask( all ) );
}


static  int     Bits( unsigned mask )
/***********************************/
{
    int     n;

    for( n = 0; mask != 0; mask &= mask - 1 ) {
        ++n;
    }
    return( n );
}


static  bool    LiveAt( conflict_node *conf, instruction *ins, block *blk )
/*************************************************************************/
{
    if( !_GBitEmpty( conf->id.out_of_block ) )
        return( _GBitOverlap( ins->head.live.out_of_block, conf->id.out_of_block ) );
    return( conf->start_block == blk
      && _LBitOverlap( ins->head.live.within_block, conf->id.within_block ) );
}


/*
 * Rows: each is a capacity and the candidates it limits, written straight
 * to the problem file; RowSeen drops exact repeats.
 */
typedef struct row_hash {
    struct row_hash *next;
    unsigned long   key;
} row_hash;

#define HASH_SIZE   4096
static  row_hash        *Seen[HASH_SIZE];
static  int             Rows;


static  bool    RowSeen( int cap, int *members, int n )
/*****************************************************/
{
    unsigned long   key;
    row_hash        *h;
    int             i;

    key = (unsigned long)cap * 2654435761UL;
    for( i = 0; i < n; ++i ) {
        key = key * 1000003UL ^ (unsigned long)members[i];
    }
    for( h = Seen[key % HASH_SIZE]; h != NULL; h = h->next ) {
        if( h->key == key ) {
            return( true );
        }
    }
    h = CGAlloc( sizeof( row_hash ) );
    h->key = key;
    h->next = Seen[key % HASH_SIZE];
    Seen[key % HASH_SIZE] = h;
    return( false );
}


static  void    FreeSeen( void )
/******************************/
{
    row_hash    *h;
    row_hash    *next;
    int         i;

    for( i = 0; i < HASH_SIZE; ++i ) {
        for( h = Seen[i]; h != NULL; h = next ) {
            next = h->next;
            CGFree( h );
        }
        Seen[i] = NULL;
    }
}


static  void    EmitRows( FILE *fp, cand *c, int n, int *live, int nlive,
                          unsigned occupied, unsigned any_bp, bool *tight )
/*************************************************************************/
{
    static const unsigned   classes[] = { CLS_WORD, CLS_INDEX, CLS_BYTE, BIT_ES };
    int                     members[512];
    int                     k;
    int                     i;
    int                     m;
    int                     cap;
    int                     load;
    unsigned                cls;

    for( k = 0; k < 4; ++k ) {
        cls = classes[k];
        if( cls != BIT_ES && !any_bp )
            cls &= ~( 1U << 6 );
        cap = Bits( cls & ~occupied );
        m = 0;
        load = 0;
        for( i = 0; i < nlive && m < 512; ++i ) {
            if( c[live[i]].mask != 0 && ( c[live[i]].mask & ~cls ) == 0 ) {
                members[m++] = live[i];
                load += c[live[i]].words;
            }
        }
        if( load <= cap )
            continue;
        *tight = true;
        if( RowSeen( cap, members, m ) )
            continue;
        fprintf( fp, "%d %d", cap, m );
        for( i = 0; i < m; ++i ) {
            fprintf( fp, " %d", members[i] );
        }
        fprintf( fp, "\n" );
        ++Rows;
    }
}


static  bool    Solve( const char *problem, const char *solution, int n, char *chosen )
/*************************************************************************************/
{
    char        cmd[1024];
    FILE        *fp;
    int         i;
    int         v;
    char        *solver;

    solver = getenv( "WCG_ILP_SOLVER" );
    if( solver == NULL )
        return( false );
    sprintf( cmd, "%s %s %s", solver, problem, solution );
    if( system( cmd ) != 0 )
        return( false );
    fp = fopen( solution, "r" );
    if( fp == NULL )
        return( false );
    for( i = 0; i < n; ++i ) {
        if( fscanf( fp, "%d", &v ) != 1 ) {
            fclose( fp );
            return( false );
        }
        chosen[i] = ( v != 0 );
    }
    fclose( fp );
    return( true );
}


void    IlpSelect( void )
/***********************/
{
    conflict_node   *conf;
    cand            *c;
    int             n;
    int             i;
    int             *live;
    int             nlive;
    block           *blk;
    instruction     *ins;
    instruction     *next;
    unsigned        occupied;
    unsigned        any_bp;
    char            *mode;
    char            *weights;
    char            problem[256];
    char            solution[256];
    FILE            *fp;
    char            *chosen;
    bool            tight;
    bool            solved;
    save_def        saved_weight[MAX_LOOP + 1];
    int             d;
    save_def        w;
    int             nchosen;

    mode = getenv( "WCG_ILP" );
    if( mode == NULL || mode[0] == '0' )
        return;
    if( DoneLabel == CurrProc->label )
        return;
    DoneLabel = CurrProc->label;
    ++Calls;
    InitWords();
    n = 0;
    for( conf = ConfList; conf != NULL; conf = conf->next_conflict ) {
        ++n;
    }
    if( n == 0 )
        return;
    c = CGAlloc( n * sizeof( cand ) );
    n = 0;
    any_bp = 0;
    for( conf = ConfList; conf != NULL; conf = conf->next_conflict ) {
        if( conf->start_block == NULL || _Is( conf, CST_CONFLICT_ON_HOLD ) || conf->savings == 0 )
            continue;
        if( conf->name->n.class != N_TEMP && conf->name->n.class != N_MEMORY )
            continue;
        if( conf->name->n.class == N_TEMP && ( conf->name->t.temp_flags & CONST_TEMP ) )
            continue;
        if( conf->name->n.size > 4 )
            continue;
        c[n].conf = conf;
        c[n].mask = PossibleMask( conf );
        c[n].words = ( conf->name->n.size > 2 ) ? 2 : 1;
        c[n].orig = conf->savings;
        c[n].obj = conf->savings;
        if( c[n].mask & ( 1U << 6 ) )
            any_bp = 1;
        ++n;
    }
    weights = getenv( "WCG_ILP_WEIGHTS" );
    if( weights != NULL && strcmp( weights, "loop" ) == 0 ) {
        memcpy( saved_weight, Save.loop_weight, sizeof( saved_weight ) );
        w = 1;
        for( d = 0; d <= MAX_LOOP; ++d ) {
            Save.loop_weight[d] = w;
            w *= 10;
        }
        for( i = 0; i < n; ++i ) {
            CalcSavings( c[i].conf );
            c[i].obj = c[i].conf->savings;
            if( c[i].obj == 0 )
                c[i].obj = 1;
            c[i].conf->savings = c[i].orig;
        }
        memcpy( Save.loop_weight, saved_weight, sizeof( saved_weight ) );
    }
    chosen = CGAlloc( n + 1 );
    for( i = 0; i < n; ++i ) {
        chosen[i] = 1;
    }
    solved = false;
    tight = false;
    if( strcmp( mode, "greedy" ) != 0 && n > 0 ) {
        sprintf( problem, "%s/wcg-ilp-%d-%d.txt", getenv( "TMPDIR" ) ? getenv( "TMPDIR" ) : "/tmp",
                 (int)getpid(), Calls );
        sprintf( solution, "%s.sol", problem );
        fp = fopen( problem, "w" );
        if( fp != NULL ) {
            fprintf( fp, "%d\n", n );
            for( i = 0; i < n; ++i ) {
                fprintf( fp, "%lu %d\n", (unsigned long)c[i].obj, c[i].words );
            }
            live = CGAlloc( n * sizeof( int ) );
            Rows = 0;
            for( blk = HeadBlock; blk != NULL; blk = blk->next_block ) {
                for( ins = blk->ins.head.next; ins->head.opcode != OP_BLOCK; ins = next ) {
                    next = ins->head.next;
                    occupied = RegMask( ins->head.live.regs ) & ( CLS_WORD | BIT_ES );
                    nlive = 0;
                    for( i = 0; i < n; ++i ) {
                        if( LiveAt( c[i].conf, ins, blk ) ) {
                            live[nlive++] = i;
                        }
                    }
                    EmitRows( fp, c, n, live, nlive, occupied, any_bp, &tight );
                    if( ins->zap != NULL && !HW_CEqual( ins->zap->reg, HW_EMPTY )
                      && next->head.opcode != OP_BLOCK ) {
                        /* the conflicts live across ins cannot sit in what it clobbers */
                        int     across = 0;
                        for( i = 0; i < nlive; ++i ) {
                            if( LiveAt( c[live[i]].conf, next, blk ) ) {
                                live[across++] = live[i];
                            }
                        }
                        EmitRows( fp, c, n, live, across,
                                  occupied | ( RegMask( ins->zap->reg ) & ( CLS_WORD | BIT_ES ) ),
                                  any_bp, &tight );
                    }
                }
            }
            CGFree( live );
            FreeSeen();
            fclose( fp );
            if( tight ) {
                solved = Solve( problem, solution, n, chosen );
            }
            if( getenv( "WCG_ILP_KEEP" ) == NULL ) {
                remove( problem );
                remove( solution );
            }
        }
    }
    nchosen = 0;
    for( i = 0; i < n; ++i ) {
        if( strcmp( mode, "greedy" ) == 0 || !solved ) {
            /* the greedy order, on the chosen weights */
            c[i].conf->savings = ( c[i].obj < CHOSEN_BASE ) ? c[i].obj : CHOSEN_BASE - 1;
        } else if( chosen[i] ) {
            ++nchosen;
            c[i].conf->savings = CHOSEN_BASE + ( ( c[i].obj < CHOSEN_BASE ) ? c[i].obj : CHOSEN_BASE - 1 );
        } else {
            c[i].conf->savings = ( c[i].obj < CHOSEN_BASE ) ? c[i].obj : CHOSEN_BASE - 1;
        }
    }
    if( getenv( "WCG_ILP_DEBUG" ) != NULL ) {
        fprintf( stderr, "ilp: %s candidates %d rows %d tight %d solved %d chosen %d\n",
                 FEName( AskForLblSym( CurrProc->label ) ), n, Rows, tight, solved, nchosen );
    }
    CGFree( chosen );
    CGFree( c );
}
