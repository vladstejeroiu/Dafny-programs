
datatype Term =
| TT
| FF
| Ite(cond: Term, thn: Term, els: Term)
| Var(x: string)
| Abs(x: string, body: Term)
| App(l: Term, r: Term)
| Amb(choices: seq<Term>)


// substitute x by t in u, t has to be closed
function method Subst(x: string, t: Term, u: Term): Term {
    match u
    case TT => TT
    case FF => FF
    case Ite(c, t1, t2) => Ite(Subst(x, t, c), Subst(x, t, t1), Subst(x, t, t2))
    case Var(y) => if x == y then t else u
    case Abs(y, b) => if x == y then u else Abs(y, Subst(x, t, b))
    case App(a, b) => App(Subst(x, t, a), Subst(x, t, b))
    case Amb(ts) => Amb(seq(|ts|, 
         i requires 0 <= i < |ts| => Subst(x, t, ts[i])))
}


// big step cbv semantics in bedrock2 postcondition-style
// returns true iff all non-deterministic branches succeed and terminate
// with a value satisfying post
inductive predicate exec(t: Term, post: Term -> bool) {
    || ((t.TT? || t.FF?) && post(t))
    || (t.Ite? && exists postC: Term -> bool :: exec(t.cond, postC) &&
                  forall c :: postC(c) ==>
                      (c.TT? || c.FF?) &&
                      (c.TT? ==> exec(t.thn, post)) &&
                      (c.FF? ==> exec(t.els, post)))
    // t.Var? means unbound variable, does not evaluate
    || (t.Abs? && post(t)) // lambda abstractions are values
    || (t.App? && (exists postL: Term -> bool :: exec(t.l, postL) &&
                   exists postR: Term -> bool :: exec(t.r, postR) &&
                   forall l2 :: postL(l2) ==>
                   forall r2 :: postR(r2) ==>
                   l2.Abs? && exec(Subst(l2.x, r2, l2.body), post)))
    || (t.Amb? && forall i :: 0 <= i < |t.choices| ==>
                  exec(t.choices[i], post))
}

lemma exec_TT(post: Term -> bool)
    requires post(TT)
    ensures exec(TT, post)
{}

lemma exec_FF(post: Term -> bool)
    requires post(FF)
    ensures exec(FF, post)
{}

lemma exec_Ite(c: Term, t1: Term, t2: Term, postC: Term -> bool, post: Term -> bool)
    requires exec(c, postC)
    requires forall c :: postC(c) ==>
                      (c.TT? || c.FF?) &&
                      (c.TT? ==> exec(t1, post)) &&
                      (c.FF? ==> exec(t2, post))
    ensures exec(Ite(c, t1, t2), post)
{}

lemma exec_Abs(x: string, t: Term, post: Term -> bool)
    requires post(Abs(x, t))
    ensures exec(Abs(x, t), post)
{}

lemma exec_App(tL: Term, tR: Term, 
    postL: Term -> bool, postR: Term -> bool, post: Term -> bool)
    requires exec(tL, postL)
    requires exec(tR, postR)
    requires forall l2 :: postL(l2) ==>
             forall r2 :: postR(r2) ==>
             l2.Abs? && exec(Subst(l2.x, r2, l2.body), post)
    ensures exec(App(tL, tR), post)
{}

lemma exec_Amb(cs: seq<Term>, post: Term -> bool)
    requires forall i :: 0 <= i < |cs| ==> exec(cs[i], post)
    ensures exec(Amb(cs), post)
{}

const And := Abs("b1", Abs("b2", Ite(Var("b1"), Var("b2"), FF)))

const Ex1 := App(App(And, Amb([TT, FF])), FF)

const AlwaysFalse := (res: Term) => res.FF?
const TrueOrFalse := (res: Term) => res.TT? || res.FF?
const Mid1 := (res: Term) => res == Abs("b2", Ite(FF, Var("b2"), FF))

/* impractical without "eapply" and unification

lemma Ex1AlwaysFalse()
    ensures exec(Ex1, AlwaysFalse)
{

    assert exec(App(And, Amb([TT, FF])), Mid1);
    assert forall l2 :: Mid1(l2) ==>
           forall r2 :: AlwaysFalse(r2) ==>
           l2.Abs? && (exec_Abs(l2.x, l2.body, Mid1); 
                       exec(Subst(l2.x, r2, l2.body), AlwaysFalse));

    exec_App(App(And, Amb([TT, FF])), FF, Mid1, AlwaysFalse, AlwaysFalse);
}
*/
