function method max(a: int, b: int): int 
{
   if a >= b then a else b
}
method Testing() {
  var v := max(2,3);
  assert v == 3;
  assert (max(2,3) == 3);
}
