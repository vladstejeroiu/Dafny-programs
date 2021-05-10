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
      high := mid;
    } else if key > a[mid] {
      low := mid + 1;
    } else {
      return mid;
    }
  } 
  
  return -1;
}
