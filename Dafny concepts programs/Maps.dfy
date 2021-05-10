
predicate Extends<K, V>(m1: map<K, V>, m2: map<K, V>) {
    forall k :: k in m2 ==> k in m1 && m1[k] == m2[k]
}

predicate UndefOn<K(!new), V>(m: map<K, V>, p: K -> bool) {
    forall k :: p(k) ==> k !in m
}

predicate Disjoint<K(!new)>(p1: K -> bool, p2: K -> bool) {
    forall k :: !(p1(k) && p2(k))
}

predicate Subset<K(!new)>(p1: K -> bool, p2: K -> bool) {
    forall k :: p1(k) ==> p2(k)
}

predicate OnlyDiffer<K(!new), V>(m1: map<K, V>, p: K -> bool, m2: map<K, V>) {
    forall k :: p(k) || (k !in m1 && k !in m2) || (k in m1 && k in m2 && m1[k] == m2[k])
}

function Diff<K>(p1: K -> bool, p2: K -> bool): K -> bool {
    k => p1(k) && !p2(k)
}


// In Coq, proving this lemma requires a user written map solver tactic, which
// took several days to develop, and used to solve the goal in about a minute,
// and after a few days of performance improvements, it can now solve the goal in 3s.
// Compare this to Dafny, which solves this goal almost instantaniously, without any
// user assistance.
lemma flattenStmt_correct_aux_lemma6<K(!new), V>(
    initialH: map<K, V>, initialL: map<K, V>, 
    fvngs: K -> bool, emv: K -> bool, av: V, vv : V,
    v: K, v0 : K, 
    prefinalL: map<K, V>, finalL: map<K, V>, 
    fvn: K -> bool, fvngs': K -> bool, mvs0: K -> bool, mvs: K -> bool
)
    requires Extends(initialL, initialH)
    requires UndefOn(initialH, fvngs)
    requires Disjoint(emv, fvngs)
    requires v in prefinalL && prefinalL[v] == av
    requires v0 in finalL && finalL[v0] == vv
    requires Subset(fvngs', fvn)
    requires Subset(fvn, fvngs)
    requires OnlyDiffer(prefinalL, mvs0, finalL)
    requires OnlyDiffer(initialL, mvs, prefinalL)
    requires mvs0(v0)
    requires mvs(v)
    requires Subset(mvs0, Diff(fvn, fvngs'))
    requires Subset(mvs, Diff(fvngs, fvn))
    ensures Extends(finalL, initialH)
{}
