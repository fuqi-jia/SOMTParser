// The callee's modifies set must lie inside the caller's: otherwise the
// caller's own frame -- "everything not in my modifies is unchanged" -- is a
// lie, and the reference implementation's CheckAssignments reports the same
// error ("command assigns to a global variable that is not in the enclosing
// procedure's modifies clause", AbsyCmd.cs over GetAssignedVariables, which
// for a call includes the callee's modifies).
var g: int;

procedure Bump();
  modifies g;

procedure P()
{
  call Bump();
}
