module Utils {
  method ArrayOfSeq<T>(s: seq<T>) returns (a: array<T>)
    ensures fresh(a)
    ensures a.Length == |s|
    ensures forall i :: 0 <= i < |s| ==> a[i] == s[i]
  {
    a := new T[|s|](i requires 0 <= i < |s| => s[i]);
  }
  
  predicate IsTotalOrder<A(!new)>(R: (A, A) -> bool) {
    // connexity
    && (forall a, b :: R(a, b) || R(b, a))
    // antisymmetry
    && (forall a, b :: R(a, b) && R(b, a) ==> a == b)
    // transitivity
    && (forall a, b, c :: R(a, b) && R(b, c) ==> R(a, c))
  }

  function method {:tailrecursive true} SetToSequence<A(!new)>(s: set<A>, R:(A, A) -> bool): seq<A>
    requires IsTotalOrder(R)
    ensures var q := SetToSequence(s, R);
    forall i :: 0 <= i < |q| ==> q[i] in s
    decreases s
{
  if s == {} then [] else
    ThereIsAMinimum(s, R);
    var x :| x in s && forall y :: y in s ==> R(x, y);
    [x] + SetToSequence(s - {x}, R)
}

lemma ThereIsAMinimum<A(!new)>(s: set<A>, R: (A, A) -> bool)
  requires s != {} && IsTotalOrder(R)
  ensures exists x :: x in s && forall y :: y in s ==> R(x, y)

}