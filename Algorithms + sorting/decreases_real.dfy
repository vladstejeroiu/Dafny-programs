method doub(a:real, b:real) returns (c:int)
    requires 0.0 < a < b
    ensures c >= 1
    decreases *
{
    var a1: real := a;
    c := 1;
    while a1 < b
        decreases *;
    {
        a1 := a1 * 2.0;
        c := c + 1;
    }
} 

method Main()
    decreases *
{
    var c:= doub(2.0, 5.0);
    print c;
}