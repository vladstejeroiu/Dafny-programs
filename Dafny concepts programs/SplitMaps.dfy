
datatype Option<T> =
| Some(getSome: T)
| None

trait K {}
trait V {}
trait Map {}

// This style is not the intended way of using Dafny.
// Just using Dafny as a quick way to encode problems into SMT with good trigger selection.

function get(m: Map, k: K): Option<V>
// keys of m2 override those of m1
function putmany(m1: Map, m2: Map): Map
// m can be split into two disjoint maps m1 and m2
predicate split(m: Map, m1: Map, m2: Map)

lemma test(m: Map, mKeep: Map, mGive: Map, frame: Map, m2: Map, mL: Map, mStack: Map)
// spec of split
requires forall M, A, B :: split(M, A, B) <==> (forall k :: 
            (exists v :: get(M, k) == Some(v) &&
                         ((get(A, k) == Some(v) && get(B, k) == None) ||
                          (get(B, k) == Some(v) && get(A, k) == None))) ||
            (get(M, k) == None && get(A, k) == None && get(B, k) == None))
// spec of putmany
requires forall m1, m2, k ::
            (exists v :: get(putmany(m1, m2), k) == Some(v) &&
                         (get(m2, k) == Some(v) || (get(m2, k) == None && get(m1, k) == Some(v)))) ||
            (get(putmany(m1, m2), k) == None && get(m2, k) == None && get(m1, k) == None)
// actual hypotheses of lemma
requires split(m, mKeep, mGive)
requires split(m2, m, mL)
requires split(mL, mStack, frame)
// conclusion
ensures split(m2, putmany(mKeep, mL), mGive)
{}
