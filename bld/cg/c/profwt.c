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
* Description:  Profile weights for the register allocator (retal-c
*               experiment).
*
*   The allocator's savings weigh each reference by its block's loop depth
*   (regsave.c Weight), and under -os every depth weighs 1. With
*   WCG_PROFILE naming a table of `source<TAB>line<TAB>count` (executions
*   per frame, tools/wcc_reglog/line_counts.py), a block weighs 1 + its
*   count instead. A block's count is the lowest of the counts of the source
*   lines its own instructions carry (each line's count is the highest of its
*   instructions', so every block on it runs at most that often); only a
*   block with no line of its own takes the line in effect where it starts. Line
*   numbers reach the code generator only with -d1, which changes no code.
*
****************************************************************************/


#include "_cgstd.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "coderep.h"
#include "data.h"
#include "cgmem.h"
#include "feprotos.h"
#include "profwt.h"


static  bool            Loaded;
static  uint_32         *LineCount;
static  uint_32         MaxLine;
static  label_handle    WeightsFor;
static  block           **WBlock;
static  uint_32         *WValue;
static  int             WCount;


static  bool    SameSource( const char *table, const char *source )
/*****************************************************************/
{
    size_t  lt;
    size_t  ls;

    lt = strlen( table );
    ls = strlen( source );
    if( lt >= ls )
        return( strcmp( table + lt - ls, source ) == 0 );
    return( strcmp( source + ls - lt, table ) == 0 );
}


static  void    Load( void )
/**************************/
{
    char        *path;
    const char  *source;
    FILE        *fp;
    char        file[512];
    unsigned long line;
    double      count;

    Loaded = true;
    path = getenv( "WCG_PROFILE" );
    if( path == NULL )
        return;
    source = FEAuxInfo( NULL, FEINF_SOURCE_NAME );
    if( source == NULL )
        return;
    fp = fopen( path, "r" );
    if( fp == NULL )
        return;
    MaxLine = 0;
    while( fscanf( fp, "%511s %lu %lf", file, &line, &count ) == 3 ) {
        if( SameSource( file, source ) && line > MaxLine ) {
            MaxLine = line;
        }
    }
    if( MaxLine == 0 ) {
        /* no line of this source in the table: keep the loop-depth weights */
        fclose( fp );
        return;
    }
    LineCount = CGAlloc( ( MaxLine + 1 ) * sizeof( uint_32 ) );
    memset( LineCount, 0, ( MaxLine + 1 ) * sizeof( uint_32 ) );
    rewind( fp );
    while( fscanf( fp, "%511s %lu %lf", file, &line, &count ) == 3 ) {
        if( SameSource( file, source ) ) {
            LineCount[line] = (uint_32)( count + 0.5 );
        }
    }
    fclose( fp );
    if( getenv( "WCG_PROFILE_DEBUG" ) != NULL ) {
        fprintf( stderr, "profwt: %s: lines up to %lu\n", source, (unsigned long)MaxLine );
    }
}


static  uint_32 CountOf( source_line_number line )
/************************************************/
{
    if( line == 0 || line > MaxLine )
        return( 0 );
    return( LineCount[line] );
}


static  void    BlockWeights( void )
/**********************************/
{
    block               *blk;
    instruction         *ins;
    source_line_number  current;
    uint_32             count;
    bool                have;
    int                 n;

    if( WBlock != NULL ) {
        CGFree( WBlock );
        CGFree( WValue );
    }
    n = 0;
    for( blk = HeadBlock; blk != NULL; blk = blk->next_block ) {
        ++n;
    }
    WBlock = CGAlloc( ( n + 1 ) * sizeof( block * ) );
    WValue = CGAlloc( ( n + 1 ) * sizeof( uint_32 ) );
    WCount = 0;
    current = 0;
    for( blk = HeadBlock; blk != NULL; blk = blk->next_block ) {
        /* the block's own lines; the one in effect at its start only if it has none */
        have = false;
        count = 0;
        for( ins = blk->ins.head.next; ins->head.opcode != OP_BLOCK; ins = ins->head.next ) {
            if( ins->head.line_num != 0 ) {
                current = ins->head.line_num;
                if( !have || CountOf( current ) < count ) {
                    count = CountOf( current );
                }
                have = true;
            }
        }
        if( !have ) {
            count = CountOf( current );
        }
        WBlock[WCount] = blk;
        WValue[WCount] = 1 + count;
        ++WCount;
    }
    WeightsFor = CurrProc->label;
}


bool    ProfileWeight( block *blk, save_def *weight )
/***************************************************/
{
    int     i;

    if( !Loaded )
        Load();
    if( LineCount == NULL )
        return( false );
    if( WeightsFor != CurrProc->label )
        BlockWeights();
    for( i = 0; i < WCount; ++i ) {
        if( WBlock[i] == blk ) {
            *weight = WValue[i];
            return( true );
        }
    }
    *weight = 1;
    return( true );
}
