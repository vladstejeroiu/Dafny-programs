class AvlNode {
    ghost var Contents: set<int>
    ghost var Repr: set<AvlNode>

    //Height of the subtree
    var height: int
    var data: int
    var left: AvlNode?
    var right: AvlNode?

  predicate Height_Valid() 
    reads this, Repr 
  {
    Valid() &&
    (left == null && right == null) ==> height == -1 &&
    (left != null && right == null) ==> height == left.height + 1 &&
    (left == null && right != null) ==> height == right.height + 1 &&
    (left != null && right != null) ==> height == max(left.height, right.height) + 1 &&
    (right != null) ==> right.Height_Valid() &&
    (left != null) ==> left.Height_Valid()
  }

  predicate Balanced() 
    reads this, Repr
  {
    Valid() &&
    Height_Valid() &&
    (left != null && right == null) ==> left.height + 1 <= 1 &&
    (left == null && right != null) ==> right.height + 1 <= 1  &&
    (left != null && right != null) ==> (right.height - left.height <= 1 && left.height - right.height <= 1) &&
    (right != null) ==> right.Balanced() &&
    (left != null) ==> left.Balanced()
  }

  function method max(a: int, b: int) : int
  {
      if (a > b) then
          a
      else 
          b
  }

  predicate Valid()
    reads this, Repr
  {
    this in Repr &&
    (left != null ==>
      left in Repr &&
      left.Repr <= Repr && this !in left.Repr &&
      left.Valid() &&
      (forall y :: y in left.Contents ==> y < data)) &&
    (right != null ==>
      right in Repr &&
      right.Repr <= Repr && this !in right.Repr &&
      right.Valid() &&
      (forall y :: y in right.Contents ==> data < y)) &&
    (left == null && right == null ==>
      Contents == {data}) &&
    (left != null && right == null ==>
      Contents == left.Contents + {data}) &&
    (left == null && right != null ==>
      Contents == {data} + right.Contents) &&
    (left != null && right != null ==>
      left.Repr !! right.Repr &&
      Contents == left.Contents + {data} + right.Contents)
  }

    constructor Init(x: int)
        ensures Valid() && fresh(Repr - {this})
        ensures Height_Valid()
        ensures Balanced()
        ensures Contents == {x}
        ensures Repr == {this};
    {
        height := 0;
        data := x;
        left := null;
        right := null;
        Contents := {x};
        Repr := {this};
    }
}