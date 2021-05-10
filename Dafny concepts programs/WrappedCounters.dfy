// Copied from https://github.com/dafny-lang/dafny/wiki/Proving-termination-by-decreasing-Repr

module V1 {
    trait Counter {
        method inc() modifies this
        method get() returns (res: nat) modifies this 
    }

    class BasicCounter extends Counter {
        var c: nat
        constructor() {
            c := 0;
        }
        method inc() 
            modifies this
        {
            c := c + 1;
        }
        method get() returns (res: nat) {
            res := c;
        }
    }

/*
    class LogWrapCounter extends Counter {
        var underlying: Counter;
        constructor(underlying: Counter) {
            this.underlying := underlying;
        }
        method inc() 
            modifies this
        {
            print "inc is called\n";
            underlying.inc(); // ERRORS
        }
        method get() returns (res: nat) {
            print "get is called\n";
            res := underlying.get(); // ERRORS
        }
    }
*/
}

module V2 {
    trait Counter {
        ghost var Repr: set<object>
        predicate Valid() reads this, Repr
        method inc() requires Valid() modifies Repr 
                     ensures Valid() && Repr == old(Repr)
        method get() returns (res: nat) requires Valid()
    }

    class BasicCounter extends Counter {
        var c: nat
        predicate Valid() reads this, Repr {
            this in Repr
        }
        constructor() ensures Valid() && fresh(Repr) {
            this.c := 0;
            this.Repr := {this};
        }
        method inc() 
            requires Valid() modifies Repr ensures Valid() && Repr == old(Repr)
        {
            c := c + 1;
        }
        method get() returns (res: nat) requires Valid() {
            res := c;
        }
    }

    /*
    class LogWrapCounter extends Counter {
        var underlying: Counter;
        predicate Valid() reads this, Repr {
            this in Repr && underlying in Repr && underlying.Repr <= Repr &&
            this !in underlying.Repr &&
            underlying.Valid()
        }
        constructor(underlying: Counter) 
            requires underlying.Valid()
            ensures Valid()
            ensures fresh(Repr - {underlying} - underlying.Repr)
        {
            this.underlying := underlying;
            this.Repr := underlying.Repr + {underlying, this};
        }
        method inc() 
            requires Valid() 
            modifies Repr     
            ensures Valid() && Repr == old(Repr)
        {
            print "inc is called\n";
            underlying.inc(); // ERROR
        }
        method get() returns (res: nat) requires Valid() {
            print "get is called\n";
            res := underlying.get(); // ERROR
        }
    }


    method infiniteLoop() {
        var b := new BasicCounter();
        var c1 := new LogWrapCounter(b);
        var c2 := new LogWrapCounter(c1);
        c1.underlying := c2;
        c1.inc();
    }
    */
}

module V3 {
    trait Counter {
        ghost var Repr: set<object>
        predicate Valid() reads this, Repr
        method inc() requires Valid() modifies Repr decreases Repr 
                     ensures Valid() && Repr == old(Repr)
        method get() returns (res: nat) requires Valid() decreases Repr
    }

    class BasicCounter extends Counter {
        var c: nat
        predicate Valid() reads this, Repr {
            this in Repr
        }
        constructor() ensures Valid() && fresh(Repr) {
            this.c := 0;
            this.Repr := {this};
        }
        method inc() 
            requires Valid() modifies Repr decreases Repr 
            ensures Valid() && Repr == old(Repr)
        {
            c := c + 1;
        }
        method get() returns (res: nat) requires Valid() decreases Repr {
            res := c;
        }
    }

    class LogWrapCounter extends Counter {
        var underlying: Counter;
        predicate Valid() reads this, Repr {
            this in Repr && underlying in Repr && underlying.Repr <= Repr &&
            this !in underlying.Repr &&
            underlying.Valid()
        }
        constructor(underlying: Counter) 
            requires underlying.Valid()
            ensures Valid()
            ensures fresh(Repr - {underlying} - underlying.Repr)
        {
            this.underlying := underlying;
            this.Repr := underlying.Repr + {underlying, this};
        }
        method inc() 
            requires Valid() 
            modifies Repr 
            decreases Repr 
            ensures Valid() && Repr == old(Repr)
        {
            print "inc is called\n";
            underlying.inc();
        }
        method get() returns (res: nat) requires Valid() decreases Repr {
            print "get is called\n";
            res := underlying.get();
        }
    }

    /*
    method infiniteLoop() {
        var b := new BasicCounter();
        var c1 := new LogWrapCounter(b);
        var c2 := new LogWrapCounter(c1);
        assert c2.Valid();
        c1.underlying := c2;
        c1.Repr := c1.Repr + c2.Repr;
        assert c1 !in c1.underlying.Repr; // fails
        c1.inc();
    }
    */

    method Main() {
        var b := new BasicCounter();
        var c1 := new LogWrapCounter(b);
        var c2 := new LogWrapCounter(c1);
        c2.inc();
        c2.inc();
        var v := c2.get();
        print v, "\n";
        c2.inc();
        v := c2.get();
        print v, "\n";
    }
}
