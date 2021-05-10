function increment(n: nat): nat
    ensures increment(n) == n + 1
{
    if n == 0 then 1 else
        (if n % 2 == 1 then 2 * increment(n / 2) else n + 1)
}