predicate sorted(a: array<int>)
  reads a
{
  if forall j, k :: 0 <= j < k < a.Length ==> a[j] <= a[k]
  then true
  else false
}

method BinarySearch(a: array<int>, key: int) returns (index: int)
  requires sorted(a)
  ensures index < 0 ==> forall k :: 0 <= k < a.Length ==> a[k] != key
  ensures index >= 0 ==> index < a.Length && a[index] == key
{
  var low, high := 0, a.Length;
  while low < high 
    invariant 0 <= low <= high <= a.Length
    invariant forall i :: 0 <= i < a.Length && !(low <= i < high) ==> a[i] != key
  {
    var mid := (low + high) / 2;
    if key < a[mid] {
	 // high := mid - 1;
     high := mid; //correct line
    } else if key > a[mid] {
	  //low := mid;
      low := mid + 1; // correct line
    } else {
      return mid;
    }
  } 
  
  return -1;
}
method Main()
  {
    var  q := new int[7]; // array of ints
    q[0], q[1], q[2] , q[3] , q[4], q[5], q[6] := 12, 10, 13 , 14 ,15,16,110;
    var x:= BinarySearch(q,10);
    print x;
  }


method MultipleReturns(x: int, y: int) returns (more: int, less: int)
  //  requires y > 0;
   ensures less < x
   ensures x < more
{
   more := x + y;
   less := x - y;
}
// Binary search using standard integers

method BinarySearch(a: array<int>, key: int) returns (r: int)
  requires forall i,j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
  ensures 0 <= r ==> r < a.Length && a[r] == key
  ensures r < 0 ==> key !in a[..]
{
  var lo, hi := 0, a.Length;
  while lo < hi
    invariant 0 <= lo <= hi <= a.Length
    invariant key !in a[..lo] && key !in a[hi..]
  {
    var mid := (lo + hi) / 2;
    if key < a[mid] {
      hi := mid;
    } else if a[mid] < key {
      lo := mid + 1;
    } else {
      return mid;
    }
  }
  return -1;
}

// Binary search using bounded integers

newtype int32 = x | -0x8000_0000 <= x < 0x8000_0000

/* This one has an overflow error:
method BinarySearchInt32_bad(a: array<int>, key: int) returns (r: int32)
  requires a.Length < 0x8000_0000
  requires forall i,j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
  ensures 0 <= r ==> r < a.Length as int32 && a[r] == key
  ensures r < 0 ==> key !in a[..]
{
  var lo, hi := 0, a.Length as int32;
  while lo < hi
    invariant 0 <= lo <= hi <= a.Length as int32
    invariant key !in a[..lo] && key !in a[hi..]
  {
    var mid := (lo + hi) / 2;  // error: possible overflow
    if key < a[mid] {
      hi := mid;
    } else if a[mid] < key {
      lo := mid + 1;
    } else {
      return mid;
    }
  }
  return -1;
}
*/

method BinarySearchInt32_good(a: array<int>, key: int) returns (r: int32)
  requires a.Length < 0x8000_0000
  requires forall i,j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
  ensures 0 <= r ==> r < a.Length as int32 && a[r] == key
  ensures r < 0 ==> key !in a[..]
{
  var lo, hi := 0, a.Length as int32;
  while lo < hi
    invariant 0 <= lo <= hi <= a.Length as int32
    invariant key !in a[..lo] && key !in a[hi..]
  {
    var mid := lo + (hi - lo) / 2;  // this is how to do it
    if key < a[mid] {
      hi := mid;
    } else if a[mid] < key {
      lo := mid + 1;
    } else {
      return mid;
    }
  }
  return -1;
}