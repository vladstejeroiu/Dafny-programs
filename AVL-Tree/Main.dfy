include "AvlTree.dfy"

method Main() {
  var tree := new AvlTree.Init();
  tree.Insert(10);
  tree.Insert(11);
  tree.Insert(12);
  tree.Insert(13);
  tree.Insert(5);
  tree.Insert(1);
  tree.Insert(6);
  tree.Insert(4);
  tree.Insert(2);
  tree.Insert(20);
  tree.Insert(21);
  tree.Insert(22);
  tree.Print();
  tree.Remove(22);
  tree.Remove(21);
  tree.Remove(20);
  tree.Remove(12);
  tree.Remove(13);
  tree.Print();

  print("\nFound 5 = ");
  var found5 := tree.Find(5);
  print(found5);
  print("\nFound 102 = ");
  var found102 := tree.Find(102);
  print(found102);
}