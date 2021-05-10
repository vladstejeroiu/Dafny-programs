function method power(a: int, n: nat): int
    requires n >= 0
{
    if n == 0 then 1 else a * power(a, n - 1)
}

// verifcation fails for Fermat's last theorem
method last(n: nat, a: nat, b: nat, c: nat) returns (res: bool)
    ensures n > 2 ==> res == false
{
    if (power(a, n) + power(b, n) == power(c, n)) {
        res := true;
    } else {
        res := false;
    }
}


