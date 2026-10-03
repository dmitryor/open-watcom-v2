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
* Description:  Global redundant register-load removal (retal-c experiment).
*
*   After register allocation the scoreboard (scmain.c) knows what each
*   register holds only along chains of single-predecessor blocks, so every
*   join and loop head starts with nothing known. This pass solves, over the
*   whole flow graph, which tracked registers hold which constant on entry to
*   each block: a forward must-analysis, the meet at a join keeping only
*   what every predecessor agrees on, iterated to a fixed point so a loop
*   head sees its back edge. A MOV whose destination already holds the
*   value is then made a no-op; the scoreboard and dead-code passes that
*   follow remove a constant load left unused.
*
*   The case it was written for: a pointer based on __segname loads ES with
*   `mov ax,SEG; mov es,ax` at every access, because the allocator never
*   keeps the segment constant in ES across a loop (x86regsv.c ConstSavings).
*
*   Deleting alone cannot help a loop whose only ES load is inside it: the
*   entry edge brings nothing, so the head's meet is unknown. Where a loop
*   head's back edges bring ES = C and only edges from outside the loop do
*   not, the load pair is inserted at the end of those outside blocks, when
*   ES and a scratch register are dead there; the in-loop load is then
*   redundant on every path and goes. One load per loop entry replaces one
*   per pass.
*
*   WCG_REGPROP=0 in the environment turns the pass off; WCG_REGPROP=1
*   removes loads without inserting any.
*
****************************************************************************/


#include "_cgstd.h"
#include <stdlib.h>
#include <string.h>
#include <stdio.h>
#include "coderep.h"
#include "data.h"
#include "cgmem.h"
#include "optab.h"
#include "makeins.h"
#include "namelist.h"
#include "insutil.h"
#include "score.h"
#include "liveinfo.h"
#include "regprop.h"


#define NREGS   7

static  hw_reg_set      Regs[NREGS];
static  name            *Top;           /* "not reached yet": the meet's identity */
static  int             Calls;
static  bool            *Loaded;        /* blocks already given a load, by index */

typedef struct {
    name        *val[NREGS];
} reg_state;


static  void    InitRegs( void )
/******************************/
{
    Regs[0] = HW_AX;
    Regs[1] = HW_BX;
    Regs[2] = HW_CX;
    Regs[3] = HW_DX;
    Regs[4] = HW_SI;
    Regs[5] = HW_DI;
    Regs[6] = HW_ES;
}


static  int     RegIndex( name *op )
/**********************************/
{
    int         i;

    if( op->n.class != N_REGISTER )
        return( -1 );
    for( i = 0; i < NREGS; ++i ) {
        if( HW_Equal( op->r.reg, Regs[i] ) ) {
            return( i );
        }
    }
    return( -1 );
}


static  void    Kill( reg_state *st, hw_reg_set regs )
/****************************************************/
{
    int         i;

    for( i = 0; i < NREGS; ++i ) {
        if( HW_Ovlap( regs, Regs[i] ) ) {
            st->val[i] = NULL;
        }
    }
}


static  void    KillAll( reg_state *st )
/**************************************/
{
    int         i;

    for( i = 0; i < NREGS; ++i ) {
        st->val[i] = NULL;
    }
}


static  bool    Step( reg_state *st, instruction *ins, bool apply )
/*****************************************************************
    Advance the state over one instruction. With apply, a MOV that would
    load a register with the value it already holds becomes a no-op.
    Returns true when it changed the instruction.
*/
{
    int         dst;
    int         src;
    name        *val;

    if( _OpIsCall( ins->head.opcode ) ) {
        KillAll( st );
        return( false );
    }
    if( ins->head.opcode == OP_MOV && ins->result != NULL && ins->num_operands == 1 ) {
        dst = RegIndex( ins->result );
        if( dst >= 0 ) {
            val = NULL;
            if( ins->operands[0]->n.class == N_CONSTANT ) {
                val = ins->operands[0];
            } else {
                src = RegIndex( ins->operands[0] );
                if( src >= 0 ) {
                    val = st->val[src];
                }
            }
            if( ins->zap != NULL ) {
                Kill( st, ins->zap->reg );
            }
            if( val != NULL && st->val[dst] == val ) {
                if( apply ) {
                    if( getenv( "WCG_REGPROP_DEBUG" ) != NULL )
                        fprintf( stderr, "regprop: drop mov to reg %d\n", dst );
                    ins->head.opcode = OP_NOP;
                    ins->num_operands = 0;
                    ins->result = NULL;
                    DoNothing( ins );
                    return( true );
                }
                return( false );
            }
            st->val[dst] = val;
            return( false );
        }
    }
    if( ins->result != NULL && ins->result->n.class == N_REGISTER ) {
        Kill( st, ins->result->r.reg );
    }
    if( ins->zap != NULL ) {
        Kill( st, ins->zap->reg );
    }
    return( false );
}


static  void    Meet( reg_state *into, reg_state *from )
/******************************************************/
{
    int         i;

    for( i = 0; i < NREGS; ++i ) {
        if( from->val[i] == Top ) {
            continue;
        }
        if( into->val[i] == Top ) {
            into->val[i] = from->val[i];
        } else if( into->val[i] != from->val[i] ) {
            into->val[i] = NULL;
        }
    }
}


static  void    Transfer( block *blk, reg_state *in, reg_state *out )
/*******************************************************************/
{
    instruction *ins;

    *out = *in;
    for( ins = blk->ins.head.next; ins->head.opcode != OP_BLOCK; ins = ins->head.next ) {
        Step( out, ins, false );
    }
}


static  void    Analyze( int n, reg_state *in, reg_state *out )
/*************************************************************/
{
    block       *blk;
    block_edge  *edge;
    reg_state   entry;
    reg_state   next;
    int         i;
    int         r;
    bool        change;

    for( i = 0; i < n; ++i ) {
        for( r = 0; r < NREGS; ++r ) {
            in[i].val[r] = Top;
            out[i].val[r] = Top;
        }
    }
    do {
        change = false;
        for( blk = HeadBlock; blk != NULL; blk = blk->next_block ) {
            if( blk == HeadBlock || blk->input_edges == NULL
              || _IsBlkAttr( blk, BLK_BIG_LABEL | BLK_RETURNED_TO ) ) {
                KillAll( &entry );
            } else {
                for( r = 0; r < NREGS; ++r ) {
                    entry.val[r] = Top;
                }
                for( edge = blk->input_edges; edge != NULL; edge = edge->next_source ) {
                    Meet( &entry, &out[edge->source->gen_blk_id] );
                }
            }
            in[blk->gen_blk_id] = entry;
            Transfer( blk, &entry, &next );
            for( r = 0; r < NREGS; ++r ) {
                if( next.val[r] != out[blk->gen_blk_id].val[r] ) {
                    change = true;
                }
            }
            out[blk->gen_blk_id] = next;
        }
    } while( change );
}


static  bool    TouchesES( instruction *ins )
/*******************************************/
{
    if( _OpIsCall( ins->head.opcode ) )
        return( true );
    if( ins->result != NULL && ins->result->n.class == N_REGISTER
      && HW_Ovlap( ins->result->r.reg, HW_ES ) )
        return( true );
    if( ins->zap != NULL && HW_Ovlap( ins->zap->reg, HW_ES ) )
        return( true );
    return( false );
}


static  bool    BlockTouchesES( block *blk )
/******************************************/
{
    instruction *ins;

    for( ins = blk->ins.head.next; ins->head.opcode != OP_BLOCK; ins = ins->head.next ) {
        if( TouchesES( ins ) ) {
            return( true );
        }
    }
    return( false );
}


static  bool    InsertLoad( block *blk, name *val )
/*************************************************
    Load ES with val at the end of blk, before its closing condition if it
    has one, when ES and a scratch register are dead there.
*/
{
    instruction *last;
    instruction *at;
    hw_reg_set  live;
    instruction *ins;
    int         i;
    bool        have_live;

    last = blk->ins.head.prev;
    while( last->head.opcode == OP_NOP && last != (instruction *)&blk->ins ) {
        last = last->head.prev;
    }
    if( _IsBlkAttr( blk, BLK_CONDITIONAL ) && last->head.opcode != OP_BLOCK ) {
        at = last;
        live = last->head.live.regs;
    } else {
        at = (instruction *)&blk->ins;
        live = blk->ins.head.live.regs;
    }
    if( Loaded[blk->gen_blk_id] || HW_Ovlap( live, HW_ES ) )
        return( false );
    for( i = 0; i < NREGS - 1; ++i ) {
        if( !HW_Ovlap( live, Regs[i] ) ) {
            break;
        }
    }
    if( i == NREGS - 1 )
        return( false );
    /*
     * Conflict nodes are stale after allocation: insert without touching
     * them, and give the new instructions the live set of where they go.
     * The scoreboard that follows rebuilds live information.
     */
    have_live = HaveLiveInfo;
    HaveLiveInfo = false;
    ins = MakeMove( val, AllocRegName( Regs[i] ), U2 );
    ResetGenEntry( ins );
    PrefixIns( at, ins );
    ins->head.live.regs = live;
    ins = MakeMove( AllocRegName( Regs[i] ), AllocRegName( HW_ES ), U2 );
    ResetGenEntry( ins );
    PrefixIns( at, ins );
    ins->head.live.regs = live;
    HW_TurnOn( ins->head.live.regs, Regs[i] );
    HaveLiveInfo = have_live;
    Loaded[blk->gen_blk_id] = true;
    if( getenv( "WCG_REGPROP_DEBUG" ) != NULL ) {
        fprintf( stderr, "regprop: load ES in block %d with reg %d %s\n",
                 (int)blk->gen_blk_id, i, at == (instruction *)&blk->ins ? "at end" : "before condition" );
    }
    return( true );
}


static  int     HoistIntoLoopEntries( reg_state *in, reg_state *out )
/********************************************************************
    For each block whose first ES write loads a constant ES does not hold
    there, climb single-predecessor blocks that leave ES alone to the join
    above it. If that join is a loop head whose in-loop predecessors all
    bring the constant, and every other predecessor is outside the loop,
    load ES at the end of those outside predecessors.
*/
{
    block       *blk;
    block       *join;
    block_edge  *edge;
    instruction *ins;
    reg_state   st;
    name        *val;
    int         dst;
    int         src;
    int         inserted;
    bool        ok;

    inserted = 0;
    for( blk = HeadBlock; blk != NULL; blk = blk->next_block ) {
        st = in[blk->gen_blk_id];
        val = NULL;
        for( ins = blk->ins.head.next; ins->head.opcode != OP_BLOCK; ins = ins->head.next ) {
            if( TouchesES( ins ) ) {
                if( ins->head.opcode == OP_MOV && ins->num_operands == 1
                  && ( dst = RegIndex( ins->result ) ) == NREGS - 1 ) {
                    src = RegIndex( ins->operands[0] );
                    if( src >= 0 && st.val[src] != NULL && st.val[src] != Top
                      && st.val[NREGS - 1] != st.val[src] ) {
                        val = st.val[src];
                    }
                }
                break;
            }
            Step( &st, ins, false );
        }
        if( val == NULL )
            continue;
        join = blk;
        while( join->inputs == 1 && join != HeadBlock
          && !_IsBlkAttr( join, BLK_LOOP_HEADER )
          && !BlockTouchesES( join->input_edges->source ) ) {
            join = join->input_edges->source;
        }
        if( !_IsBlkAttr( join, BLK_LOOP_HEADER ) || join == HeadBlock )
            continue;
        ok = true;
        for( edge = join->input_edges; edge != NULL; edge = edge->next_source ) {
            if( out[edge->source->gen_blk_id].val[NREGS - 1] == val )
                continue;
            if( edge->source->depth >= join->depth ) {
                ok = false;
            }
        }
        if( !ok )
            continue;
        for( edge = join->input_edges; edge != NULL; edge = edge->next_source ) {
            if( out[edge->source->gen_blk_id].val[NREGS - 1] != val ) {
                if( InsertLoad( edge->source, val ) ) {
                    ++inserted;
                    /* now ES = val leaving it; recount on the next analysis */
                    out[edge->source->gen_blk_id].val[NREGS - 1] = val;
                }
            }
        }
    }
    return( inserted );
}


static  bool    IndexUsesES( name *op )
/*************************************/
{
    return( op != NULL && op->n.class == N_INDEXED && op->i.index != NULL
      && op->i.index->n.class == N_REGISTER && HW_Ovlap( op->i.index->r.reg, HW_ES ) );
}


static  bool    UsesES( instruction *ins )
/****************************************
    ES read as an operand, a segment override operand, or the segment half
    of an ES:reg index, in an operand or in the result (a store).
*/
{
    opcnt       i;
    name        *op;

    for( i = 0; i < ins->num_operands; ++i ) {
        op = ins->operands[i];
        if( op->n.class == N_REGISTER && HW_Ovlap( op->r.reg, HW_ES ) )
            return( true );
        if( IndexUsesES( op ) )
            return( true );
    }
    return( IndexUsesES( ins->result ) );
}


static  void    ExtendESLiveness( int n )
/****************************************
    Inserted loads make ES live out of blocks whose stored live-out sets
    predate them. Solve ES liveness over the graph and turn ES on in every
    block live-out that needs it (never off: the stored sets stay a safe
    over-approximation), then rebuild each instruction's live set.
*/
{
    block       *blk;
    block       *son;
    instruction *ins;
    bool        *gen;
    bool        *kill;
    bool        *live_in;
    bool        out;
    bool        in;
    bool        change;
    block_num   e;
    int         id;

    gen = CGAlloc( n * sizeof( bool ) );
    kill = CGAlloc( n * sizeof( bool ) );
    live_in = CGAlloc( n * sizeof( bool ) );
    for( blk = HeadBlock; blk != NULL; blk = blk->next_block ) {
        id = blk->gen_blk_id;
        gen[id] = false;
        kill[id] = false;
        live_in[id] = false;
        for( ins = blk->ins.head.next; ins->head.opcode != OP_BLOCK; ins = ins->head.next ) {
            if( !kill[id] && UsesES( ins ) )
                gen[id] = true;
            if( TouchesES( ins ) )
                kill[id] = true;
        }
    }
    do {
        change = false;
        for( blk = HeadBlock; blk != NULL; blk = blk->next_block ) {
            id = blk->gen_blk_id;
            out = HW_Ovlap( blk->ins.head.live.regs, HW_ES );
            for( e = 0; e < blk->targets; ++e ) {
                if( blk->edge[e].flags & BEF_DEST_IS_BLOCK ) {
                    son = blk->edge[e].destination.u.blk;
                    if( live_in[son->gen_blk_id] ) {
                        out = true;
                    }
                }
            }
            if( out && !HW_Ovlap( blk->ins.head.live.regs, HW_ES ) ) {
                HW_TurnOn( blk->ins.head.live.regs, HW_ES );
                change = true;
            }
            in = gen[id] || ( out && !kill[id] );
            if( in != live_in[id] ) {
                live_in[id] = in;
                change = true;
            }
        }
    } while( change );
    if( getenv( "WCG_REGPROP_DEBUG" ) != NULL ) {
        for( blk = HeadBlock; blk != NULL; blk = blk->next_block ) {
            id = blk->gen_blk_id;
            fprintf( stderr, "regprop: block %d gen %d kill %d in %d out %d\n", id, gen[id], kill[id],
                     live_in[id], HW_Ovlap( blk->ins.head.live.regs, HW_ES ) );
        }
    }
    CGFree( gen );
    CGFree( kill );
    CGFree( live_in );
    LiveInfoUpdate();
}


void    RegPropagate( void )
/**************************/
{
    block       *blk;
    reg_state   *in;
    reg_state   *out;
    reg_state   entry;
    instruction *ins;
    int         n;
    int         inserted;
    char        *env;
    name        top_name;
    block_id    *saved;

    env = getenv( "WCG_REGPROP" );
    if( env != NULL && env[0] == '0' )
        return;
    /* WCG_REGPROP_MAX=n: only the first n procedures, to bisect */
    ++Calls;
    if( getenv( "WCG_REGPROP_MAX" ) != NULL && Calls > atoi( getenv( "WCG_REGPROP_MAX" ) ) )
        return;
    InitRegs();
    Top = &top_name;
    n = 0;
    for( blk = HeadBlock; blk != NULL; blk = blk->next_block ) {
        ++n;
    }
    /* gen_blk_id holds each block's index here; restored at the end */
    saved = CGAlloc( n * sizeof( block_id ) );
    n = 0;
    for( blk = HeadBlock; blk != NULL; blk = blk->next_block ) {
        saved[n] = blk->gen_blk_id;
        blk->gen_blk_id = n++;
    }
    in = CGAlloc( n * sizeof( reg_state ) );
    out = CGAlloc( n * sizeof( reg_state ) );
    Loaded = CGAlloc( n * sizeof( bool ) );
    memset( Loaded, 0, n * sizeof( bool ) );
    Analyze( n, in, out );
    inserted = 0;
    if( env == NULL || env[0] != '1' ) {
        inserted = HoistIntoLoopEntries( in, out );
        if( inserted != 0 ) {
            Analyze( n, in, out );
        }
    }
    for( blk = HeadBlock; blk != NULL; blk = blk->next_block ) {
        int     r;
        entry = in[blk->gen_blk_id];
        for( r = 0; r < NREGS; ++r ) {
            if( entry.val[r] == Top ) {
                entry.val[r] = NULL;
            }
        }
        for( ins = blk->ins.head.next; ins->head.opcode != OP_BLOCK; ins = ins->head.next ) {
            Step( &entry, ins, true );
        }
    }
    if( inserted != 0 ) {
        ExtendESLiveness( n );
    }
    n = 0;
    for( blk = HeadBlock; blk != NULL; blk = blk->next_block ) {
        blk->gen_blk_id = saved[n++];
    }
    CGFree( Loaded );
    CGFree( saved );
    CGFree( in );
    CGFree( out );
}
