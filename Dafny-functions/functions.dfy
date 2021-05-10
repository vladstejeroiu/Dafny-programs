// double
function double<T>(f: T -> T): T -> T 
    ensures double(f) == ((x: T) => f(f(x)))
{
    (x: T) => f(f(x))
}

method testDouble() {
    assert double(inc)(6) == ((x: int) => x + 2)(6);
    assert double(inc)(6) == 8;
}

// composition
function compose<T>(f: T -> T, g: T -> T): T -> T
    ensures compose(f, g) == ((x: T) => f(g(x)))
{   
    (x: T) => f(g(x))
}

method testCompose() {
    assert compose(square, inc)(7) == ((x: int) => (x + 1) * (x + 1))(7);
    assert compose(square, inc)(6) == 49;
    assert compose(square, inc)(0) == 1;
}

function gcd(a: int, b: int): int 
    requires a >= 0 && b >= 0 && b <= a
    ensures gcd(a, b) == 0 ==> a == 0 || b == 0
    ensures gcd(a, b) == 0 <==> a == 0
    ensures a != 0 ==> (a % gcd(a, b)) == 0
    ensures exists c:int :: c * gcd(a, b) == a
    ensures exists c:int :: c * gcd(a, b) == b
{
    if b == 0 then a else gcd(b, a % b)
}

function square(x: int): int 
    decreases x
    ensures square(x) == x * x
{
    x * x
}

function method inc(x: int): int 
    decreases x
    ensures inc(x) - x == 1
{
    x + 1
}

function twice(x: real): real
    ensures twice(x) == x * 2.0
{
    x * 2.0
}

/*
    McCarthy's function 91: nested recursion
// function f91t(n: nat, k: nat): nat
//     decreases n, 100 - n, k
// {
//     if k == 0 then n else if n > 100 then f91t(n - 10, k - 1) else f91t(n + 11, k + 1)
// }

// method f(n: nat) returns (res: nat) 
//     decreases 100 - n, 100 - f(n + 11)
// {
//     if n > 100 {
//         return n - 10;
//     }

//     assert n <= 100;
//     // res := n;
//     // while  res <= 100 {
//     //     res := res + 11;
//     // }
//     var x := f(n + 11);
//     res := f(x);
// }





