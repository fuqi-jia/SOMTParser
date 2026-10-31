procedure P(value: int) returns (result: int);
    ensures result == value;

// Renaming is legal, but changing a parameter's type is not.
implementation P(input: bool) returns (output: int) {
    output := 0;
}
