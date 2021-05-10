datatype Pair = Pair(first: int, second: int)

function make_rat(n: int, d: int): Pair
    ensures make_rat(n, d) == Pair(n, d)
{
    Pair(n, d)
}

function numer(n: Pair): int
    ensures numer(n) == n.first
{
    n.first 
}

function denom(n: Pair): int
    ensures denom(n) == n.second
{
    n.second
}

predicate eq(n1: Pair, n2: Pair)
{
    numer(n1) * denom(n2) == numer(n2) * denom(n1)
}

function add_rat(n1: Pair, n2: Pair): Pair 
    ensures numer(add_rat(n1, n2)) == numer(n1) * denom(n2) + numer(n2) * denom(n1)
    ensures denom(add_rat(n1, n2)) == denom(n1) * denom(n2)
{
    Pair(numer(n1) * denom(n2) + numer(n2) * denom(n1), denom(n1) * denom(n2))
}

function sub_rat(n1: Pair, n2: Pair): Pair 
    ensures numer(add_rat(n1, n2)) == numer(n1) * denom(n2) + numer(n2) * denom(n1)
    ensures denom(add_rat(n1, n2)) == denom(n1) * denom(n2)
{
    Pair(numer(n1) * denom(n2) + numer(n2) * denom(n1), denom(n1) * denom(n2))
}
