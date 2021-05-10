function fib(n: nat): nat
    decreases n
{
   if n == 0 then 0 else
   if n == 1 then 1 else
                  fib(n - 1) + fib(n - 2)
}

method ComputeFib(n: nat) returns (b: nat)
   ensures b == fib(n)
{
   var i: int := 0;
   b := 0;
   var a := 1;
   while i < n
      invariant 0 <= i <= n
      invariant b == fib(i)
      invariant a == fib(i + 1)
      decreases n - i
   {
      b, a  := a, a + b;
      i := i + 1;
   }
}

method Testing()
{   
    var v := ComputeFib(3);
    assert (v == 2);
}