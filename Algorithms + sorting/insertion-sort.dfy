
/* Algorithm 
To sort an array of size n in ascending order: 
1: Iterate from arr[1] to arr[n] over the array. 
2: Compare the current element (key) to its predecessor. 
3: If the key element is smaller than its predecessor, compare it to the elements before. Move the greater elements one position up to make space for the swapped element.
*/

predicate sorted_between(A:array<int>, from:int, to:int)
    reads A
{
    forall i, j :: 0 <= i <= j < A.Length && from <= i <= j <= to ==> A[i] <= A[j]
}

predicate sorted(A:array<int>)
    reads A
{
    sorted_between(A, 0, A.Length-1)
}


method InsertionSort(A:array<int>)
    modifies A
    requires A.Length >= 1
    ensures multiset(A[..]) == multiset(old(A[..]))
    ensures sorted(A)
{
    var N := A.Length;
    var i := 1;
    while i < N
        invariant 1 <= i <= N
        invariant multiset(A[..]) == multiset(old(A[..]))
        invariant sorted_between(A, 0, i-1)
        decreases N-i
    {
        print A[..], "\n";
        var j := i;
        while j > 0 && A[j-1] > A[j] 
            invariant 1 <= i <= N-1
            invariant 0 <= j <= i
            invariant multiset(A[..]) == multiset(old(A[..]))
            invariant forall m, n :: 0 <= m < n < i+1 && n != j ==> A[m] <= A[n]
            decreases j
        {
            A[j], A[j-1] := A[j-1], A[j];
            j := j-1;
            print A[..], "\n";
        }
        i := i+1;
        print "\n";
    }
}

method Main() {
    var A := new int[10];
    A[0], A[1], A[2], A[3], A[4], A[5], A[6], A[7], A[8], A[9] := 2, 4, 6, 15, 3, 19, 17, 16, 18, 1;
    InsertionSort(A);
    print A[..];
}

/* Explanation:

invariant forall m, n :: 0 <= m <n <i + 1 && n! = j ==> A [m] <= A [n]
     // A is ordered for each pair of elements
     // except for those where the index of the second element is equal to j

*/