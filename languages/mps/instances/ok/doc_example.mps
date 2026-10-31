* The example from docs/languages/mps.md §2.1.
NAME          EXAMPLE
ROWS
 N  COST
 L  LIM1
 G  LIM2
 E  MYEQN
COLUMNS
    MARKER                 'MARKER'                 'INTORG'
    XONE      COST         1.0        LIM1         1.0
    MARKER                 'MARKER'                 'INTEND'
    YTWO      COST         2.0        LIM1         1.0
    YTWO      MYEQN       -1.0
    ZTHREE    LIM2         1.0
RHS
    RHS       LIM1         4.0        LIM2         10.0
RANGES
    RNG       LIM1         2.5
BOUNDS
 UP BND       XONE         4.0
ENDATA
