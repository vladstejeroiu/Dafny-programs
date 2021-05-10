// TestSet1 fails to verify
method TestSet1() {
  assert (set x: int | x in {-2, -1, 0, 1, 2} :: x * 2) == {-4, -2, 0, 2, 4};
}

// if and only if operator, <==>, does not work
function Intersection<T>(s1: set<T>, s2: set<T>): set<T>
  ensures forall x :: x in s1 && x in s2 ==> x in Intersection(s1, s2)
  ensures forall x :: x in Intersection(s1, s2) ==> x in s1 && x in s2
{
  set x | x in s1 && x in s2
}

// Union fails to verify:
// Dafny uses syntactic heuristics to determine whether a set comprehension is finite
// The heuristics depend on type of the bound variables or conjuncts that constrain elements to be bounded
// Dafny has no syntactic heuristic for proving a bound for disjunctions
function Union<T>(s1: set<T>, s2: set<T>): set<T>
  ensures forall x :: x in s1 || x in s2 <==> x in Union(s1, s2)
{
  set x | x in s1 || x in s2
}




// references: 
// https://stackoverflow.com/questions/50195891/how-do-i-write-a-clean-function-in-dafny-to-get-the-minimum-of-a-set
// https://stackoverflow.com/questions/49398650/dafny-what-does-no-terms-found-to-trigger-on-mean

// A trigger is a syntactic pattern involving quantified variables that serves as heuristic for the solver to do something with the quantifier. 
// With a forall quantifier, the trigger tells Dafny when to instantiate the quantified formula with other expressions. 
// Otherwise, Dafny will never use the quantified formula.
method max(s: set<int>) returns (m: int) 
    requires |s| > 0
    ensures forall k :: k in s ==> k <= m
{ 
  var e :| e in s;
  if (|s| >  1)  {
      var r := max(s - {e});
      m := (if e > r then e else r);
      
      // postcondition is not met without this
      // however it gives a warning: 'no terms found to trigger on'
      assert forall k :: k in (s - {e}) ==> m >= k; 

      assert m >= e;
  } else {
      assert |s - {e}| == 0;
      return e;
  }
}




function Pick(s: set<int>): int
  requires |s| > 0
{
  var x :| x in s; x
} 

// taken from: http://leino.science/papers/krml274.html
lemma Choices(s: set<int>)
  requires s != {}
{
  var a := Pick(s);
  var b := Pick(s);
  // this is provable since the same :| operator is used
  // Placing it in a function guarantees that on the same argument, the same results is returned on every execution
  assert a == b;
  a := var x :| x in s; x;
  b := var x :| x in s; x;
  assert a == b;  // error: not provable
}