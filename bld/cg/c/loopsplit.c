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
* Description:  Live-range splitting at loop boundaries (retal-c experiment).
*
*   The allocator decides register or memory for a temporary over its whole
*   live range. A value used heavily inside one loop and live, but rarely
*   used, around it gets one decision for both stretches. Before conflicts
*   are built, this pass gives each such temporary a fresh name inside the
*   loop:
*
*       preheader:      MOV t -> t'         when t is live into the loop
*       loop blocks:    every reference to t becomes t'
*       exit targets:   MOV t' -> t         when t is live there
*
*   so the allocator sees two conflicts and can keep t' in a register in the
*   loop and t in memory around it (the moves become a load and a store), or
*   give both the same register (the moves vanish). Loops are taken
*   innermost first, so an outer loop splits the copies an inner one made.
*
*   A temporary is split only when it is a plain front-end variable (no
*   address taken, not volatile, no aliases, integral and at most 4 bytes),
*   and only when every exit target that needs the copy back is entered
*   from the loop alone (no edge splitting).
*
*   A loop is split only when the profile (WCG_PROFILE, profwt.c) says it
*   goes round at least WCG_SPLIT_RATIO times (default 8) per entry: the
*   copies run at every entry and exit.
*
*   WCG_SPLIT=1 enables it; WCG_SPLIT_MAX=n stops after n splits per
*   compile, to bisect; WCG_SPLIT_DEBUG traces.
*
****************************************************************************/


#include "_cgstd.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "coderep.h"
#include "data.h"
#include "cgmem.h"
#include "makeins.h"
#include "namelist.h"
#include "insutil.h"
#include "indvars.h"
#include "loopopts.h"
#include "feprotos.h"
#include "profwt.h"
#include "loopsplit.h"


extern block        *Head;
extern block        *PreHead;
extern block        *Loop;

static  int         Splits;
static  int         MaxSplits = -1;
static  bool        Debug;
static  int         Ratio;


static  bool    Refers( name *op, name *t )
/*****************************************/
{
    if( op == NULL )
        return( false );
    if( op == t )
        return( true );
    if( op->n.class == N_INDEXED && ( op->i.index == t || op->i.base == t ) )
        return( true );
    return( false );
}


static  name    *Rename( name *op, name *t, name *nt )
/****************************************************/
{
    name    *index;
    name    *base;

    if( op == NULL )
        return( op );
    if( op == t )
        return( nt );
    if( op->n.class == N_INDEXED && ( op->i.index == t || op->i.base == t ) ) {
        index = ( op->i.index == t ) ? nt : op->i.index;
        base = ( op->i.base == t ) ? nt : op->i.base;
        return( ScaleIndex( index, base, op->i.constant, op->n.type_class,
                            op->n.size, op->i.scale, op->i.index_flags ) );
    }
    return( op );
}


static  bool    Splittable( name *t )
/***********************************/
{
    if( t->n.class != N_TEMP )
        return( false );
    if( t->t.temp_flags & ( CONST_TEMP | STACK_PARM | ALIAS | CG_INTRODUCED ) )
        return( false );
    if( t->t.alias != t )
        return( false );
    if( t->v.usage & ( USE_ADDRESS | VAR_VOLATILE | NEEDS_MEMORY | USE_MEMORY ) )
        return( false );
    if( !_IsIntegral( t->n.type_class ) && t->n.type_class != PT && t->n.type_class != CP )
        return( false );
    if( t->n.size == 0 || t->n.size > 4 || t->n.size != TypeClassSize[t->n.type_class] )
        return( false );
    return( true );
}


/*
 * Liveness of one temporary over the flow graph, by block index.
 */
static  int         NBlocks;
static  block       **Blocks;
static  bool        *LiveIn;


static  int     BlockIndex( block *blk )
/**************************************/
{
    return( (int)blk->gen_blk_id );
}


static  void    NumberBlocks( block_id **saved )
/**********************************************/
{
    block   *blk;
    int     n;

    n = 0;
    for( blk = HeadBlock; blk != NULL; blk = blk->next_block ) {
        ++n;
    }
    NBlocks = n;
    Blocks = CGAlloc( ( n + 1 ) * sizeof( block * ) );
    LiveIn = CGAlloc( ( n + 1 ) * sizeof( bool ) );
    *saved = CGAlloc( ( n + 1 ) * sizeof( block_id ) );
    n = 0;
    for( blk = HeadBlock; blk != NULL; blk = blk->next_block ) {
        (*saved)[n] = blk->gen_blk_id;
        blk->gen_blk_id = n;
        Blocks[n++] = blk;
    }
}


static  void    UnnumberBlocks( block_id *saved )
/***********************************************/
{
    int     i;

    for( i = 0; i < NBlocks; ++i ) {
        Blocks[i]->gen_blk_id = saved[i];
    }
    CGFree( saved );
    CGFree( Blocks );
    CGFree( LiveIn );
}


static  void    Liveness( name *t )
/*********************************/
{
    bool        *gen;
    bool        *kill;
    bool        change;
    bool        out;
    bool        in;
    block       *blk;
    instruction *ins;
    opcnt       i;
    block_num   e;
    int         b;
    bool        used;

    gen = CGAlloc( NBlocks * sizeof( bool ) );
    kill = CGAlloc( NBlocks * sizeof( bool ) );
    for( b = 0; b < NBlocks; ++b ) {
        blk = Blocks[b];
        gen[b] = false;
        kill[b] = false;
        LiveIn[b] = false;
        for( ins = blk->ins.head.next; ins->head.opcode != OP_BLOCK; ins = ins->head.next ) {
            used = false;
            for( i = 0; i < ins->num_operands; ++i ) {
                if( Refers( ins->operands[i], t ) ) {
                    used = true;
                }
            }
            if( ins->result != NULL && ins->result != t && Refers( ins->result, t ) )
                used = true;
            if( ins->result == t && TypeClassSize[ins->type_class] < t->n.size )
                used = true;   /* a partial definition keeps the rest */
            if( used && !kill[b] )
                gen[b] = true;
            if( ins->result == t && TypeClassSize[ins->type_class] >= t->n.size )
                kill[b] = true;
        }
    }
    do {
        change = false;
        for( b = NBlocks; b-- > 0; ) {
            blk = Blocks[b];
            out = false;
            for( e = 0; e < blk->targets; ++e ) {
                if( ( blk->edge[e].flags & BEF_DEST_IS_BLOCK )
                  && LiveIn[BlockIndex( blk->edge[e].destination.u.blk )] ) {
                    out = true;
                }
            }
            in = gen[b] || ( out && !kill[b] );
            if( in != LiveIn[b] ) {
                LiveIn[b] = in;
                change = true;
            }
        }
    } while( change );
    CGFree( gen );
    CGFree( kill );
}


/*
 * Candidates: the splittable temporaries referenced in the current loop.
 */
static  name    **Cands;
static  int     NCands;
static  int     CapCands;


static  void    AddCand( name *op )
/*********************************/
{
    int     i;

    if( op == NULL )
        return;
    if( op->n.class == N_INDEXED ) {
        if( op->i.index != NULL )
            AddCand( op->i.index );
        if( op->i.base != NULL && op->i.base->n.class == N_TEMP )
            AddCand( op->i.base );
        return;
    }
    if( !Splittable( op ) )
        return;
    for( i = 0; i < NCands; ++i ) {
        if( Cands[i] == op ) {
            return;
        }
    }
    if( NCands == CapCands ) {
        name    **more;

        CapCands = CapCands ? CapCands * 2 : 64;
        more = CGAlloc( CapCands * sizeof( name * ) );
        if( NCands )
            memcpy( more, Cands, NCands * sizeof( name * ) );
        if( Cands )
            CGFree( Cands );
        Cands = more;
    }
    Cands[NCands++] = op;
}


static  bool    ExitTargetOk( block *target )
/*******************************************
    The copy back can go at the start of target only if every way into
    target comes from the loop.
*/
{
    block_edge  *edge;

    for( edge = target->input_edges; edge != NULL; edge = edge->next_source ) {
        if( !_IsBlkAttr( edge->source, BLK_IN_LOOP ) ) {
            return( false );
        }
    }
    return( true );
}


static  int     SplitLoop( void )
/*******************************/
{
    block       *blk;
    block       *target;
    instruction *ins;
    instruction *move;
    opcnt       i;
    block_num   e;
    int         c;
    int         done;
    name        *t;
    name        *nt;
    bool        live_in;
    bool        need_out;
    bool        ok;
    block_id    *saved;

    /*
     * Each split costs its copies at every entry and exit, so split only a
     * loop the profile says goes round at least Ratio times per entry.
     */
    {
        save_def    head_w;
        save_def    pre_w;

        block_edge  *in;
        save_def    w;

        ProfileRefresh();
        if( !ProfileWeight( Head, &head_w ) || !ProfileWeight( PreHead, &pre_w ) )
            return( 0 );
        /*
         * A preheader the loop optimiser added has no line of its own; count
         * entries from the blocks that enter it (an upper bound).
         */
        if( PreHead->input_edges != NULL ) {
            pre_w = 1;
            for( in = PreHead->input_edges; in != NULL; in = in->next_source ) {
                ProfileWeight( in->source, &w );
                pre_w += w - 1;
            }
        }
        /* no count for the entries (an entry block with no line): unpriced, leave it */
        if( head_w <= 1 || pre_w <= 1 || head_w < (save_def)Ratio * pre_w ) {
            if( Debug )
                fprintf( stderr, "split: loop with %lu entries, %lu passes: no\n",
                         (unsigned long)pre_w - 1, (unsigned long)head_w - 1 );
            return( 0 );
        }
        if( Debug )
            fprintf( stderr, "split: loop with %lu entries, %lu passes: split\n",
                     (unsigned long)pre_w - 1, (unsigned long)head_w - 1 );
    }
    NCands = 0;
    for( blk = Loop; blk != NULL; blk = blk->u.loop ) {
        for( ins = blk->ins.head.next; ins->head.opcode != OP_BLOCK; ins = ins->head.next ) {
            for( i = 0; i < ins->num_operands; ++i ) {
                AddCand( ins->operands[i] );
            }
            AddCand( ins->result );
        }
    }
    done = 0;
    NumberBlocks( &saved );
    for( c = 0; c < NCands; ++c ) {
        if( MaxSplits >= 0 && Splits >= MaxSplits )
            break;
        t = Cands[c];
        Liveness( t );
        live_in = LiveIn[BlockIndex( Head )];
        need_out = false;
        ok = true;
        for( blk = Loop; blk != NULL && ok; blk = blk->u.loop ) {
            for( e = 0; e < blk->targets; ++e ) {
                if( ( blk->edge[e].flags & BEF_DEST_IS_BLOCK ) == 0 )
                    continue;
                target = blk->edge[e].destination.u.blk;
                if( _IsBlkAttr( target, BLK_IN_LOOP ) )
                    continue;
                if( LiveIn[BlockIndex( target )] ) {
                    need_out = true;
                    if( !ExitTargetOk( target ) ) {
                        ok = false;
                    }
                }
            }
        }
        if( !ok || ( !live_in && !need_out ) )
            continue;
        nt = SAllocTemp( t->n.type_class, t->n.size );
        for( blk = Loop; blk != NULL; blk = blk->u.loop ) {
            for( ins = blk->ins.head.next; ins->head.opcode != OP_BLOCK; ins = ins->head.next ) {
                for( i = 0; i < ins->num_operands; ++i ) {
                    ins->operands[i] = Rename( ins->operands[i], t, nt );
                }
                ins->result = Rename( ins->result, t, nt );
            }
        }
        if( live_in ) {
            SuffixPreHeader( MakeMove( t, nt, t->n.type_class ) );
        }
        if( need_out ) {
            for( blk = Loop; blk != NULL; blk = blk->u.loop ) {
                for( e = 0; e < blk->targets; ++e ) {
                    if( ( blk->edge[e].flags & BEF_DEST_IS_BLOCK ) == 0 )
                        continue;
                    target = blk->edge[e].destination.u.blk;
                    if( _IsBlkAttr( target, BLK_IN_LOOP ) || !LiveIn[BlockIndex( target )] )
                        continue;
                    /* once per target: the first instruction is our copy if it is there */
                    move = target->ins.head.next;
                    if( move->head.opcode == OP_MOV && move->operands[0] == nt && move->result == t )
                        continue;
                    PrefixIns( target->ins.head.next, MakeMove( nt, t, t->n.type_class ) );
                }
            }
        }
        ++Splits;
        ++done;
    }
    UnnumberBlocks( saved );
    return( done );
}


void    LoopSplit( void )
/***********************/
{
    block       *blk;
    block       **headers;
    int         n;
    int         i;
    int         j;
    int         total;
    bool        have_live;
    char        *env;

    env = getenv( "WCG_SPLIT" );
    if( env == NULL || env[0] == '0' )
        return;
    if( MaxSplits < 0 && getenv( "WCG_SPLIT_MAX" ) != NULL )
        MaxSplits = atoi( getenv( "WCG_SPLIT_MAX" ) );
    Debug = ( getenv( "WCG_SPLIT_DEBUG" ) != NULL );
    Ratio = getenv( "WCG_SPLIT_RATIO" ) ? atoi( getenv( "WCG_SPLIT_RATIO" ) ) : 8;
    n = 0;
    for( blk = HeadBlock; blk != NULL; blk = blk->next_block ) {
        if( _IsBlkAttr( blk, BLK_LOOP_HEADER ) ) {
            ++n;
        }
    }
    if( n == 0 )
        return;
    headers = CGAlloc( n * sizeof( block * ) );
    n = 0;
    for( blk = HeadBlock; blk != NULL; blk = blk->next_block ) {
        if( _IsBlkAttr( blk, BLK_LOOP_HEADER ) ) {
            headers[n++] = blk;
        }
    }
    /* innermost first */
    for( i = 1; i < n; ++i ) {
        blk = headers[i];
        for( j = i; j > 0 && headers[j - 1]->depth < blk->depth; --j ) {
            headers[j] = headers[j - 1];
        }
        headers[j] = blk;
    }
    have_live = HaveLiveInfo;
    HaveLiveInfo = false;
    total = 0;
    for( i = 0; i < n; ++i ) {
        Head = headers[i];
        MarkLoop();
        total += SplitLoop();
        UnMarkLoop();
    }
    HaveLiveInfo = have_live;
    ProfileRefresh();
    CGFree( headers );
    if( Cands != NULL ) {
        CGFree( Cands );
        Cands = NULL;
        NCands = CapCands = 0;
    }
    if( Debug && total != 0 ) {
        fprintf( stderr, "split: %s: %d loops, %d temporaries split\n",
                 FEName( AskForLblSym( CurrProc->label ) ), n, total );
    }
}
