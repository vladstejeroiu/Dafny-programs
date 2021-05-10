
class Counter {
    ghost var Repr: set<object>
    var c: nat
    predicate Valid() reads this, Repr {
        this in Repr
    }
    constructor() ensures Valid() && fresh(Repr) {
        this.c := 0;
        this.Repr := {this};
    }
    method Inc(amount: nat) 
        requires Valid() 
        modifies Repr
        ensures Valid() && Repr == old(Repr)
    {
        c := c + amount;
    }
    method Get() returns (res: nat) requires Valid() {
        res := c;
    }
}

class FourCounters {
    ghost var Repr: set<object>
    var c1: Counter
    var c2: Counter
    var c3: Counter
    var c4: Counter
    predicate Valid() reads this, Repr {
        && this in Repr
        && c1 in Repr && c1.Repr <= Repr
        && c2 in Repr && c2.Repr <= Repr
        && c3 in Repr && c3.Repr <= Repr
        && c4 in Repr && c4.Repr <= Repr
        && c1.Valid() && c2.Valid() && c3.Valid() && c4.Valid()
        && this !in c1.Repr && this !in c2.Repr && this !in c3.Repr && this !in c4.Repr 
        && (c1.Repr !! c2.Repr !! c3.Repr !! c4.Repr)
    }
    constructor() ensures Valid() && fresh(Repr) {
        c1 := new Counter();
        c2 := new Counter();
        c3 := new Counter();
        c4 := new Counter();
        new;
        Repr := {this, c1, c2, c3, c4} + c1.Repr + c2.Repr + c3.Repr + c4.Repr;
    }
    method Rotate() 
        requires Valid()
        modifies Repr
        ensures Valid()
    {
        c1, c2, c3, c4 := c4, c1, c2, c3;
    }
    method Inc()
        requires Valid()
        modifies Repr
        ensures Valid()
        ensures Repr == old(Repr)
    {
        c1.Inc(1);
        c2.Inc(2);
        c3.Inc(3);
        c4.Inc(4);
    }
}

class FourNCounters {
    ghost var Repr: set<object>
    var counters: array<FourCounters?>
    predicate Valid() reads this, Repr {
        && this in Repr
        && counters in Repr
        && (forall i :: 0 <= i < counters.Length && counters[i] != null ==>
                counters[i] in Repr &&
                counters[i].Repr <= Repr &&
                counters[i].Valid() &&
                this !in counters[i].Repr)
        && forall i, j :: 0 <= i < j < counters.Length &&
                          counters[i] != null && counters[j] != null
                      ==> counters[i].Repr !! counters[j].Repr
    }
    constructor(size: nat) 
        ensures Valid()
        ensures counters.Length == size
        ensures forall i :: 0 <= i < size ==> counters[i] == null
        ensures fresh(Repr)
    {
        counters := new FourCounters?[size](i => null);
        Repr := {this, counters};
    }
    method Import(i: nat, c: FourCounters)
        requires i < counters.Length
        requires counters[i] == null
        requires c.Valid()
        requires Valid()
        requires c.Repr !! Repr
        modifies Repr
        ensures Valid()
        ensures Repr == old(Repr) + c.Repr
        ensures counters.Length == old(counters.Length)
        ensures counters[i] == c
        ensures forall j :: 0 <= j < counters.Length && j != i ==>
                    counters[j] == old(counters[j])
    {
        counters[i] := c;
        Repr := Repr + c.Repr;
    }
    method UnImport(i: nat) returns (c: FourCounters)
        requires Valid()
        requires i < counters.Length
        requires counters[i] != null;
        modifies Repr
        ensures Valid()
        ensures counters.Length == old(counters.Length)
        ensures counters[i] == null
        // ensures Repr == old(Repr) - c.Repr // TODO
    {
        c := counters[i];
        counters[i] := null;
    }
    method IncAll()
        requires Valid()
        modifies Repr
    {
        ghost var origRepr := Repr;
        var i: nat := 0;
        while (i < counters.Length) 
            invariant Valid()
            invariant Repr == origRepr;
        {
            if (counters[i] != null) {
                counters[i].Inc();
                // TODO
                assert counters[i] != null;
                assert counters[i].Valid();
            }
            i := i + 1;
        }
    }
}

method Main() {
    var a1 := new FourNCounters(10);
    var a2 := new FourNCounters(5);
    var c1 := new FourCounters();
    var c2 := new FourCounters();
    a1.Import(1, c1);
    a1.Import(2, c2);

}