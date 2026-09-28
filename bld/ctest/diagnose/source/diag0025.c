/* Test pointer truncation warnings for based pointers converted to near
 * pointers. The segment of a based pointer is dropped by such a conversion,
 * just as it is for a far pointer.
 */

__segment               seg;
char __based( seg )     *bp;
char __based( void )    *vp;
char __based( __segname( "_DATA" ) )    *dp;
char __based( __segname( "OTHER" ) )    *op;
char                    *np;
char __far              *fp;

void takes_near( char *p )
{
    (void)p;
}

char *return_near( void )
{
    return( bp );           // W112
}

char __based( seg ) *return_based( void )
{
    return( np );           // OK
}

int main( void )
{
    np = bp;                // W112
    np = vp;                // W112
    np = op;                // W112
    np = dp;                // OK: _DATA is the default data segment
    np = (char *)bp;        // OK: explicit cast
    takes_near( bp );       // W112
    takes_near( (char *)bp );   // OK: explicit cast
    bp = np;                // OK: no segment is lost
    bp = fp;                // OK: no warning as before
    fp = bp;                // OK
    vp = (char __based( void ) *)bp;    // OK
    return( 0 );
}
