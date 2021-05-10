
class Counter {
    ghost var Repr: set<object>
    predicate Valid() 
        reads this
    {
        this in Repr
    }
    var c: nat
    method Inc(amount: nat) 
        requires Valid()
        modifies Repr
        ensures Valid()
        ensures Repr == old(Repr)
    {
        c := c + amount;
    }
    method Get() returns (res: nat) {
        res := c;
    }
    constructor() 
        ensures Valid()
        ensures fresh(Repr)
    {
        c := 0;
        Repr := {this};
    }
}

class ThreeCounters {
    var c1: Counter
    var c2: Counter
    var c3: Counter
    ghost var Repr: set<object>
    predicate Valid() reads this, Repr {
        && c1 in Repr && c2 in Repr && c3 in Repr
        && c1.Repr <= Repr && c2.Repr <= Repr && c3.Repr <= Repr
        && c1.Valid() && c2.Valid() && c3.Valid()
        && this !in c1.Repr + c2.Repr + c3.Repr
    }
    constructor()
        ensures Valid()
        ensures fresh(Repr)
    {
        c1 := new Counter();
        c2 := new Counter();
        c3 := new Counter();
        new;
        Repr := c1.Repr + c2.Repr + c3.Repr;
    }
    method Inc() 
        requires Valid()
        modifies Repr
        ensures Valid()
    {
        c1.Inc(1);
        assert c2.Valid(); // <-- assertion violation
        c2.Inc(2);
        c3.Inc(3);
    }
}

method Main() {
    var tc1 := new ThreeCounters();
    tc1.Inc();
    tc1.Inc(); // Calling it the second time doesn't work any more
}