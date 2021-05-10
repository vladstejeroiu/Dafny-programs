
method LinealSearch(A:array<int>, key:int) returns (index:int)
    ensures 0 <= index ==> index < A.Length && A[index] == key
    ensures index < 0 ==> key !in A[..]
{
    var N := A.Length;
    var i := 0;
    while i < N
        invariant 0 <= i <= N
        // Ningún elemento tal que su índice sea menor al actual puede ser el elemento buscado
        invariant forall k :: 0 <= k < i ==> A[k] != key
        decreases N - i
    {
        if A[i] == key
        {
            return i;
        }
        i := i + 1;
    }
    return -1;
}

method Main() {
    var a := new int[10];
    a[0], a[1], a[2], a[3], a[4], a[5], a[6], a[7], a[8], a[9] := 2, 4, 6, 8, 10, 12, 14, 16, 18, 20;
    var index := LinealSearch(a, 12);
    print index;
}

/* Explicación:

invariant forall k :: 0 <= k < i ==> A[k] != key
    // Ningún elemento tal que su índice sea menor al actual puede ser el elemento buscado

*/
