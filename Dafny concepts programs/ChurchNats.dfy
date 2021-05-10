
include "./Std.dfy"

datatype Term =
| Var(x: string)
| Abs(x: string, body: Term)
| App(l: Term, r: Term)
{
    function method ToString(): string 
        decreases this
    {
        match this {
            case Var(x) => x
            case Abs(x, body) => "(\\" + x + ". " + body.ToString() + ")"
            case App(l, r) => "(" + l.ToString() + " " + r.ToString() + ")"
        }
    }
}

// substitute x by t in u, t has to be closed
function method Subst(x: string, t: Term, u: Term): Term {
    match u {
        case Var(y) => if x == y then t else u
        case Abs(y, b) => if x == y then u else Abs(y, Subst(x, t, b))
        case App(a, b) => App(Subst(x, t, a), Subst(x, t, b))
    }
}

predicate Step(t1: Term, t2: Term) {
    //     (\x. b) c --> b[c/x]
    || (t1.App? && t1.l.Abs? && t2 == Subst(t1.l.x, t1.r, t1.l.body))

    //       a --> b
    //     -----------
    //     a c --> b c
    || (t1.App? && t2.App? && Step(t1.l, t2.l) && t2.r == t1.r)

    //        a --> b
    //      -----------
    //      c a --> c b
    || (t1.App? && t2.App? && t2.l == t1.l && Step(t1.r, t2.r))
}

inductive predicate MultiStep(t1: Term, t2: Term) {
    t1 == t2 || exists tmid :: Step(t1, tmid) && MultiStep(tmid, t2)
}

method cbv(t: Term) returns (r: Std.Option<Term>)
    decreases * // <-- disables termination checker
{
    match t {
        case Var(x) => return Std.None;
        case Abs(x, b) => return Std.Some(t);
        case App(t1, t2) =>
            /* Extracting Options can be very verbose:
            var tmp1 := cbv(t1);
            if tmp1.None? { return Std.None; }
            var u1 := tmp1.get;
            var tmp2 := cbv(t2);
            if tmp2.None? { return Std.None; }
            var u2 := tmp2.get;
            if !u2.Abs? { return Std.None; }
            var Abs(x, b) := u2; 
            r := cbv(Subst(x, u2, b));
            */

            /* Shorter syntax: */
            var u1: Term :- cbv(t1); 
            var u2: Term :- cbv(t2); 
            if !u2.Abs? { return Std.None; }
            var Abs(x, b) := u2; 
            r := cbv(Subst(x, u2, b));

            /* Desugars to:
            var tmp1 := cbv(t1);
            if tmp1.IsFailure() { return tmp1.PropagateFailure(); }
            var u1 := tmp1.Extract();
            var tmp2 := cbv(t2);
            if tmp2.IsFailure() { return tmp2.PropagateFailure(); }
            var u2 := tmp2.Extract();
            if !u2.Abs? { return Std.None; }
            var Abs(x, b) := u2; 
            r := cbv(Subst(x, u2, b));
            */
    }
}

function method ssssz(n: nat): Term {
    if n == 0 then Var("z") else App(Var("s"), ssssz(n-1))
}

function method NatToChurch(n: nat): Term {
    Abs("s", Abs("z", ssssz(n)))
}

const Add: Term :=
    // \n m s z. n s (m s z)
    Abs("n", Abs("m", Abs("s", Abs("z", 
      App(App(Var("n"), Var("s")), App(App(Var("m"), Var("s")), Var("z")))))))

const TwoPlusThree: Term :=
    App(App(Add, NatToChurch(2)), NatToChurch(3))

method PrintSomeChurchNumerals(upTo: nat) {
    var i := 0;
    while (i < upTo) {
        print i, ": ", NatToChurch(i).ToString(), "\n";
        i := i + 1;
    }
}

method Main() 
    decreases *
{
    PrintSomeChurchNumerals(4);
    var r := cbv(App(App(Add, NatToChurch(2)), NatToChurch(3)));
    if r.Some? { print r.get.ToString(), "\n"; }
}
