method Main() {
  while false {
    var r := 2 + 2;
    var a := 2;
    var c := 10 * 4 + 5 + a;
  }
}

method MultipleReturns(x: int, y: int) returns (more: int, less: int)
{
  more := x + y;
  less := x - y;
}


function update(s: seq<int>, i: int, v: int): seq<int>
   requires 0 <= i < |s|
   ensures update(s, i, v) == s[i := v]
{
  s[..i] + [v] + s[i+1..]
}

// counts the numbers of True elements in the given sequence
function countTrue(a: seq<bool>): nat
{
  if |a| == 0 then 0 else
  (if a[0] then 1 else 0) + countTrue(a[1..])
}

lemma DistributiveLemma(a: seq<bool>, b: seq<bool>)
  ensures countTrue(a + b) == countTrue(a) + countTrue(b)
{
  if a == [] {
    assert a + b == b;
  } else {
    DistributiveLemma(a[1..], b);
    assert a + b == [a[0]] + (a[1..] + b);
  }
}

// returns the length
function Length<T>(a: seq<T>): int
  ensures Length(a) == |a|
{
  if |a| == 0 then 0 else 1 + Length(a[1..])
}

// reverses all elements
function Reverse<T>(a: seq<T>): seq<T>
  ensures |Reverse(a)| == |a|
  ensures forall k :: 0 <= k < |a| ==> Reverse(a)[k] == a[|a| - k - 1] 
{
  if |a| == 0 || |a| == 1 then a else Reverse(a[1..]) + [a[0]]
}

// squares all elements
function Square(a: seq<int>): seq<int>
  ensures |Square(a)| == |a|
  ensures forall k :: 0 <= k < |a| ==> Square(a)[k] == a[k] * a[k]
{
  if |a| == 0 then [] else [a[0] * a[0]] + Square(a[1..])
}

method square(a: array<int>)
  modifies a
  ensures a[..] == Square(old(a[..]))
{ 
  var test := a[1..2];
  var i := 0;
  while i < a.Length 
    invariant 0 <= i <= a.Length
    invariant i == 0 && i < a.Length ==> a[i] == old(a[i]) 
    invariant forall k :: 0 <= k < a.Length && k >= i ==> a[k] == old(a[k])
    invariant forall k :: 0 <= k < i ==> a[k] == old(a[k]) * old(a[k])
  {
    a[i] := a[i] * a[i];
    i := i + 1;
  }
}

// filters elements according to a given predicate
function Filter<T>(a: seq<T>, pred: ((T) -> bool)): seq<T>
  ensures |Filter(a, pred)| <= |a|
  ensures forall k :: 0 <= k < |Filter(a, pred)| ==> Filter(a, pred)[k] in a
  ensures forall k :: 0 <= k < |Filter(a, pred)| ==> pred(Filter(a, pred)[k])
{
  if |a| == 0 then [] else 
    (if pred(a[0]) then [a[0]] else []) + Filter(a[1..], pred)
}

// map elements according to a given function
function Map<T, S>(a: seq<T>, f: ((T) -> S)): seq<S> 
  ensures |Map(a, f)| == |a|
  ensures forall k :: 0 <= k < |a| ==> Map(a, f)[k] == f(a[k])
{
  if |a| == 0 then [] else [f(a[0])] + Map(a[1..], f)
}

method map_method<T, A>(a: array<T>, f: ((T) -> T))
  modifies a
  ensures a[..] == Map(old(a[..]), f)
{
  var i := 0;
  while i < a.Length 
    invariant 0 <= i <= a.Length
    invariant forall k :: 0 <= k < a.Length && k >= i ==> a[k] == old(a[k])
    invariant forall k :: 0 <= k < i ==> a[k] == f(old(a[k]))
  {
    a[i] := f(a[i]);
    i := i + 1;
  }
}



function Append<T>(e: T, s: seq<T>): seq<T> 
  ensures |Append(e, s)| == |s| + 1 // length should be 1 greater than the original
  ensures Append(e, s)[..|Append(e, s)|-1] == s // the sequences should be exactly the same except for the new element
  ensures Append(e, s)[|Append(e, s)|-1] == e // last element should be e
{
  s + [e]
}

// removes the first occurrence of e in s
// returns the original sequence if there is no occurrence
function Remove<T>(e: T, s: seq<T>): seq<T>
  ensures count(e, s) == 0 ==> Remove(e, s) == s // sequences should remain the same
  ensures count(e, s) > 0 ==> |Remove(e, s)| == |s| - 1 // length should be 1 less than original
  // ensures count(e, s) > 0 ==> count(e, Remove(e, s)) == count(e, s) - 1 // number of e's should be 1 less than original
  // the first e in the new sequence should be at a greater or equal index compared to the original
{
  if |s| == 0 then [] else
    (if s[0] == e then s[1..] else [s[0]] + Remove(e, s[1..]))
}

function Accumulate<T>(op: (T, seq<T>) -> seq<T>, initial: seq<T>, s: seq<T>): seq<T>
{
  if |s| == 0 then initial else
    (
        op(
          s[0], 
          Accumulate(op, initial, s[1..])
        )
    )
}

// TODO
// function Permutation<T>(a: seq<T>): seq<seq<T>> 
//   ensures forall k :: 0 <= k < |Permutation(a)| ==> |Permutation(a)[k]| == |a| // all permutations have the same length as the original sequence
//   ensures forall k :: 0 <= k < |Permutation(a)| ==> 
//     forall j :: 0 <= j < |a|
//       ==> count(Permutation(a)[k][j], Permutation(a)[k]) == count(Permutation(a)[k][j], a) // for each permutation, the count of each element is the same as the original sequence
// {
//   if |a| == 0 then [[]] else 
//     Accumulate(
//       Append, [], Map(
//         a, 
//         (x: T) => Map(
//           Permutation(Remove(x, a)), 
//           (p: seq<T>) => [x] + p
//         )
//       )
//     )
// }


function count<T>(e: T, a: seq<T>): int 
  ensures 0 <= count(e, a) <= |a| // redundant
  ensures count(e, a) == multiset(a)[e]
{
  multiset(a)[e]
}

// swaps elements at the given indices
method swap(a: array<int>, i: int, j: int)
  requires 0 <= i < a.Length
  requires 0 <= j < a.Length
  modifies a
  ensures a[i] == old(a[j])
  ensures a[j] == old(a[i])
  ensures forall k :: 0 <= k < a.Length && k != i && k != j ==> a[k] == old(a[k])
  ensures a.Length == old(a.Length)
{
  while true {
      a[i], a[j] := a[j], a[i];
      break;
  }
}
