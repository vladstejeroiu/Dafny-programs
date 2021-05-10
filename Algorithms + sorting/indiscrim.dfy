// nondeterministic
method A(a: int) returns (x: int)
{
    // indiscriminate choices
    if * {
    assert true;
    } else if * {
    assert true;
    } else {
    assert true;
    }

    if
    case true =>  x := 1;
    case true =>  x := 2;
    case true =>  x := 3;
}

method Main()
{
    var a := A(1);
    print a;
}