var total: int;

// Declarations need not precede their implementations. The different formal
// names are matched by position; old(total) names this body's entry state.
implementation Add(amount: int) returns (previous: int) {
    previous := total;
    total := total + amount;
}

procedure Add(delta: int) returns (before: int);
    requires delta >= 0;
    modifies total;
    ensures before == old(total);
    ensures total == old(total) + delta;

procedure Client()
    modifies total;
    requires total == 3;
{
    var oldTotal: int;
    call oldTotal := Add(2);
    assert oldTotal == 3 && total == 5;
}
