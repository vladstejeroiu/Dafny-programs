// unchanged: specifies all fields are the same as that in the pre-state

method scale(v: array<real>, scalar: real) returns (v2: array<real>) 
  modifies v
  ensures unchanged(v)
  ensures fresh(v2)
  ensures v2.Length == v.Length
  ensures forall k :: 0 <= k < v2.Length ==> v2[k] == v[k] * scalar
{
    var i := 0;
    v2 := new real[v.Length];
    assert v2.Length == v.Length;
    while i < v.Length
      invariant unchanged(v)
      invariant 0 <= i <= v.Length
      invariant forall k :: 0 <= k < i ==> v2[k] == v[k] * scalar
    {
      v2[i] := v[i] * scalar;
      i := i + 1;
    }
}

method normalize(v: array<real>) returns (v2: array<real>) 
  modifies v
  ensures unchanged(v)
  ensures fresh(v2)
  ensures v2.Length == v.Length
  ensures forall k :: 0 <= k < v2.Length ==> v2[k] == v[k] / (v.Length as real)
{
    var i := 0;
    v2 := new real[v.Length];
    assert v2.Length == v.Length;
    while i < v.Length
      invariant unchanged(v)
      invariant 0 <= i <= v.Length
      invariant forall k :: 0 <= k < i ==> v2[k] == v[k] / (v.Length as real)
    {
      v2[i] := v[i] / (v.Length as real);
      i := i + 1;
    }
}

method add(v1: array<real>, v2: array<real>) returns (v3: array<real>) 
  requires v1.Length == v2.Length
  modifies v1
  modifies v2
  ensures unchanged(v1, v2)
  ensures fresh(v3)
  ensures v3.Length == v1.Length == v2.Length
  ensures forall k :: 0 <= k < v3.Length ==> v3[k] == v1[k] + v2[k]
{
    var i := 0;
    v3 := new real[v1.Length];
    assert v3.Length == v1.Length == v2.Length;
    while i < v1.Length
      invariant unchanged(v1)
      invariant unchanged(v2)
      invariant 0 <= i <= v1.Length && i <= v2.Length
      invariant forall k :: 0 <= k < i ==> v3[k] == v1[k] + v2[k]
    {
      v3[i] := v1[i] + v2[i];
      i := i + 1;
    }
}

method Add(v1: array<array<real>>, v2: array<array<real>>) returns (v3: array<array<real>>) 
  requires v1.Length == v2.Length
  requires forall i :: 0 <= i < v1.Length ==> v1[i].Length == v2[i].Length
  modifies v1
  modifies v2
  ensures unchanged(v1, v2)
  ensures v3.Length == v1.Length == v2.Length
  ensures forall i :: 0 <= i < v1.Length ==> v3[i].Length == v1[i].Length == v2[i].Length
  ensures forall i :: 0 <= i < v3.Length ==> forall j :: 0 <= j < v3[i].Length ==> v3[i][j] == v1[i][j] + v2[i][j]
{
    var i := 0;
    v3 := new array<real>[v1.Length];
    assert v3.Length == v1.Length == v2.Length;
    while i < v1.Length
      invariant unchanged(v1)
      invariant unchanged(v2)
      invariant 0 <= i <= v1.Length && i <= v2.Length
      invariant forall k :: 0 <= k < i ==> v3[k].Length == v1[k].Length == v2[k].Length
      invariant forall k :: 0 <= k < i ==> forall m :: 0 <= m < v3[k].Length ==> v3[k][m] == v1[k][m] + v2[k][m]
    {
      v3[i] := new real[v1[i].Length];
      var j := 0;
      while j < v1[i].Length
        modifies v3[i]
        invariant unchanged(v1)
        invariant unchanged(v2)
        invariant v3[i].Length == v1[i].Length == v2[i].Length
        invariant 0 <= i < v1.Length && i < v2.Length
        invariant 0 <= j <= v1[i].Length && j <= v2[i].Length
        invariant forall m :: 0 <= m < j ==> v3[i][m] == v1[i][m] + v2[i][m]
      {
        v3[i][j] := v1[i][j] + v2[i][j];
        j := j + 1;
      }
      i := i + 1;
    }
}

method subtract(v1: array<real>, v2: array<real>) returns (v3: array<real>) 
  requires v1.Length == v2.Length
  modifies v1
  modifies v2
  ensures unchanged(v1, v2)
  ensures fresh(v3)
  ensures v3.Length == v1.Length == v2.Length
  ensures forall k :: 0 <= k < v3.Length ==> v3[k] == v1[k] + (v2[k] * -1.0)
{ 
  var v2_neg := scale(v2, -1.0);
  v3 := add(v1, v2_neg);

  // var i := 0;
  // v3 := new real[v1.Length];
  // assert v3.Length == v1.Length == v2.Length;
  // while i < v1.Length
  //   invariant unchanged(v1)
  //   invariant unchanged(v2)
  //   invariant 0 <= i <= v1.Length
  //   invariant 0 <= i <= v2.Length
  //   invariant forall k :: 0 <= k < i ==> v3[k] == v1[k] - v2[k]
  // {
  //   v3[i] := v1[i] - v2[i];
  //   i := i + 1;
  // }
}

method multiply(v1: array<real>, v2: array<real>) returns (v3: array<real>) 
  requires v1.Length == v2.Length
  modifies v1
  modifies v2
  ensures unchanged(v1, v2)
  ensures v3.Length == v1.Length == v2.Length
  ensures forall k :: 0 <= k < v3.Length ==> v3[k] == v1[k] * v2[k]
{   
  var i := 0;
  v3 := new real[v1.Length];
  assert v3.Length == v1.Length == v2.Length;
  while i < v1.Length
    invariant unchanged(v1)
    invariant unchanged(v2)
    invariant 0 <= i <= v1.Length
    invariant 0 <= i <= v2.Length
    invariant forall k :: 0 <= k < i ==> v3[k] == v1[k] * v2[k]
  {
    v3[i] := v1[i] * v2[i];
    i := i + 1;
  }
}

function method Sum(v: array<real>, i: int): real
  requires 0 <= i < v.Length
  reads v
{
  if i == 0 then v[i] else v[i] + Sum(v, i - 1)
}
