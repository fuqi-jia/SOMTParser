* §2.2. The FIRST N row is the objective; later ones are free rows constraining
* nothing. Treating the second as a constraint invents one the file does not
* have. The convention is not universal, so the choice is warned.
ROWS
 N  COST
 N  FREEROW
 G  R1
COLUMNS
    X         COST         1.0        FREEROW      5.0
    X         R1           1.0
RHS
    RHS       R1           2.0
ENDATA
