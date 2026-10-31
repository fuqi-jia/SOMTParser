* §2.3. The MARKER lines are POSITIONAL STATE, invisible in any single column
* line. Ignoring them makes every variable continuous, which is the LP
* RELAXATION of the model -- complete = true, sound = false, and a strictly
* easier and different problem whose optimum is reported as this one's.
ROWS
 N  OBJ
 G  R1
COLUMNS
    MARKER                 'MARKER'                 'INTORG'
    I1        OBJ          1.0        R1           1.0
    I2        OBJ          1.0        R1           1.0
    MARKER                 'MARKER'                 'INTEND'
    C1        OBJ          1.0        R1           1.0
RHS
    RHS       R1           2.0
ENDATA
