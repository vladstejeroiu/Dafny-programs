predicate method isReversed(s: array<char>, r: array<char>)
    reads s, r
    requires s.Length == r.Length
{
    forall i :: 0 <= i < s.Length ==> s[i] == r[s.Length - i - 1]
}


method StringReverse(s: array<char>) returns (r: array<char>)

  // add in any pre- or post-conditions you need here!
  requires s.Length > 0
  ensures s.Length == r.Length
  ensures isReversed(s, r)           // ensure r is correctly reversed
{
    r := new char[s.Length];
    var i := 0;
    var j := s.Length - 1;
    r[i] := s[j];
    i := i + 1;
    j := j - 1;
    while i < s.Length
        decreases s.Length - i
        invariant 0 <= i <= s.Length
        invariant j == s.Length - i - 1
        invariant forall k :: 0 <= k < i ==> r[k] == s[s.Length - k - 1]
    {
        r[i] := s[j];
        i := i + 1;
        j := j - 1;
    }
}


