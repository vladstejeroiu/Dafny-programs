

class {:autocontracts} Conjunto
{
    var content: array<nat>;
    var size: nat;
    ghost var GhostSet: seq<nat>;

    predicate Valid()
    {
        content[0..size] == GhostSet
        && 0 <= size <= content.Length
        && forall i,j :: 0 <= i < size
        && 0 <= j < size
        && i != j ==> content[i] != content[j]
    }

    constructor ()
    ensures GhostSet == []
    {
        content := new nat[10];
        size := 0;
        GhostSet := [];
    }

    method Contains(element:nat) returns (success:bool)
    requires size < content.Length;
    ensures success <=> element in GhostSet;
    {
        success := false;
        var i := 0;
        while(i < size)
        invariant 0<=i<=size
        invariant (i > 0) ==> b == (element in GhostSet[0..i])
        invariant (i == 0) ==> !b
        decreases size - i
        {
            if(content[i] == element){
                success := true;
            }
            i := i + 1;
        }
        return success;
    }

    method Intersection(inputSet: Conjunto) returns (newIntersection: Conjunto)
    requires |GhostSet| >= 0
    requires |inputSet.GhostSet| >= 0
    ensures |newIntersection.GhostSet| >= 0
    ensures forall i:: (0 <= i< |newIntersection.GhostSet|) ==> newIntersection.GhostSet[i] in inputSet.GhostSet
    ensures forall i:: (0 <= i< |newIntersection.GhostSet|) ==> newIntersection.GhostSet[i] in GhostSet
    ensures forall i,j :: (0 <= i < |newIntersection.GhostSet|)
                        && (0 <= j < |newIntersection.GhostSet|)
                        && (i != j) ==> newIntersection.GhostSet[i]
                        != newIntersection.GhostSet[j]
    {
        var i := 0;
        
        newIntersection := new Conjunto();
        newIntersection.size := size + inputSet.size;
        newIntersection.content := new nat[size + inputSet.size];
        newIntersection.GhostSet := [];

        while(i < size)
        decreases size - i
        invariant 0 <= i <= size
        {
            var verify := inputSet.Contains(content[i]);
            if(verify)
            {
                var b := newIntersection.Add(content[i]);
            }
            i := i + 1;
        }

    }

    method Add(element:nat) returns (success:bool)
    ensures element in old(GhostSet) ==> |GhostSet| == |old(GhostSet)|
    ensures !(element in old(GhostSet)) ==> size == old(size) + 1
    ensures element in old(GhostSet) ==> (GhostSet == old(GhostSet)) && success == false
    ensures !(element in old(GhostSet)) ==> (GhostSet == old(GhostSet) + [element]) && success == true
    {
        var verify := Contains(element);
        if(!verify){
            if(size == content.Length)
            {
                var newSize := new nat[2 * content.Length];
                var i := 0;
                forall(i | 0 <= i <= size-1)
                {
                    newSize[i] := content[i];
                }
                content := newSize;
            }
            content[size] := element;
            size := size + 1;
            GhostSet := GhostSet + [element];
            success := !verify;
        } else {
            success := !verify;
        }
    }

    method Size() returns (total:nat)
    requires size >= 0
    ensures total == |GhostSet|
    {
        return size;
    }

    method Union(inputSet: Conjunto) returns (newSet: Conjunto)
    requires |GhostSet| >= 0
    requires |inputSet.GhostSet| >= 0
    ensures forall i :: (0 <= i< |inputSet.GhostSet|) ==> inputSet.GhostSet[i] in newSet.GhostSet
    ensures |newSet.GhostSet| >= 0
    ensures |newSet.GhostSet| <= |GhostSet| + |inputSet.GhostSet|
    {
        newSet := new Conjunto();
        newSet.size := size + inputSet.size;
        newSet.content := new nat[size + inputSet.size];
        newSet.GhostSet := [];

        var i := 0;
        var j := 0;
        while(i < size)
        decreases size - i
        invariant 0 <= i <= size
        {
            var b := newSet.Add(content[i]);
            i := i + 1;
        }

        while(j < inputSet.size)
        decreases inputSet.size - j
        invariant 0 <= j <= inputSet.size
        {
            var verify := Contains(inputSet.content[size+j]);
            if(!verify){
                var b := newSet.Add(inputSet.content[size+j]);
            }
            j := j + 1;
        }

    }

    method Difference(setTest: Conjunto) returns (newSet: Conjunto)
    requires |setTest.GhostSet| >= 0
    ensures |newSet.GhostSet| >= 0                
    ensures forall i :: (0 <= i < |newSet.GhostSet|) ==> ((newSet.GhostSet[i] in setTest.GhostSet && !(newSet.GhostSet[i] in GhostSet)) || !(newSet.GhostSet[i] in setTest.GhostSet) && (newSet.GhostSet[i] in GhostSet))
    {
        newSet := new Conjunto();
        newSet.size := size + setTest.size;
        newSet.content := new nat[size + setTest.size];
        newSet.GhostSet := [];

        var i := 0;
        var k := 0;
        while(i < size)
        decreases size - i
        invariant 0 <= i <= size
        {
            var verify := Contains(content[i]);
            if(!verify){
                var b := newSet.Add(content[i]);
            }
            i := i + 1;
        }

        while(k < setTest.size)
        decreases setTest.size - k
        invariant 0 <= k <= setTest.size
        {
            var verify := Contains(setTest.content[k]);
            if(!verify){
                var b := newSet.Add(setTest.content[k]);
            }
            k := k + 1;
        }
    }
}

method Main()
{
    var conjunto1 := new Conjunto();
    assert conjunto1.GhostSet == [];
    var t1 := conjunto1.Add(4);
    assert conjunto1.GhostSet == [4];
    t1 := conjunto1.Add(12);
    t1 := conjunto1.Add(78);
    t1 := conjunto1.Add(9);
    t1 := conjunto1.Add(6);
    t1 := conjunto1.Add(7);
    t1 := conjunto1.Add(99); 
    assert t1 ==  true;
    t1 := conjunto1.Add(7);
    assert t1 == false;

    t1 := conjunto1.Contains(78);
    assert t1 == true;
    t1 := conjunto1.Contains(10);
    assert t1 == false;

    var t2 := conjunto1.Size();
    assert t2 == 7;
    assert |conjunto1.GhostSet| == 7;
   
    var conjunto2 := new Conjunto();
    var t3 := conjunto2.Add(8);
    t3 := conjunto2.Add(7);
    t3 := conjunto2.Add(9);
    t3 := conjunto2.Add(1);
    t3 := conjunto2.Add(3);

    var unionSet := conjunto1.Union(conjunto2);
    assert unionSet.size == 8;

    var interSet := conjunto1.Intersection(conjunto2);
    assert interSet.size == 2;

    var diffSet := conjunto1.Difference(conjunto2);
}