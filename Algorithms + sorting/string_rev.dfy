predicate method isReversed(s: seq<char>, r: seq<char>)
    requires |s| == |r|
{
    forall i :: 0 <= i < |s| ==> s[i] == r[|s| - i - 1]
}


method StringReverse(s: seq<char>) returns (r: seq<char>)

  // add in any pre- or post-conditions you need here!
  requires |s| > 0
  ensures |s| == |r|
  ensures isReversed(s, r)           // ensure r is correctly reversed
{
    r := [];
    var i := 0;
    var j := |s| - 1;
    r := r + [s[j]];
    i := i + 1;
    j := j - 1;
    while i < |s|
        decreases |s| - i
        invariant 0 <= i <= |s|
        invariant j == |s| - i - 1
        invariant forall k :: 0 <= k < i ==> r[k] == s[|s| - k - 1]
    {
        r := r + [s[j]];
        i := i + 1;
        j := j - 1;
    }
}
