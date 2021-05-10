
// <exp> ::= <num> + <num>
//        |  <num> - <num>
//        |  <num> * <num>
//        |  <num> / <num>
//        |  <num> % <num>

datatype Exp = Literal(x: int) | Plus(x: Exp, y: Exp) | Minus(x: Exp, y: Exp) | Times(x: Exp, y: Exp) | Divide(x: Exp, y: Exp) | Mod(x: Exp, y: Exp)
type Val = int

function method plus(x: int, y: int): int
    ensures plus(x, y) == x + y
{
    x + y
}

function method minus(x: int, y: int): int
    ensures minus(x, y) == x - y
{
    x - y
}

function method times(x: int, y: int): int
    ensures times(x, y) == x * y
{
    x * y    
}

function method divide(x: int, y: int): int
    requires y != 0
    ensures divide(x, y) == x / y
{
    x / y
}

function method mod(x: int, y: int): int
    requires y != 0
    ensures mod(x, y) == x % y
{
    x % y
}

function method eval(e: Exp): (res: Val)
    ensures e == Literal(e.x) ==> res == e.x 
    ensures e == Plus(e.x, e.y) ==> res == plus(eval(e.x), eval(e.y))
    ensures e == Minus(e.x, e.y) ==> res == minus(eval(e.x), eval(e.y))
    ensures e == Times(e.x, e.y) ==> res == times(eval(e.x), eval(e.y))
    ensures e == Divide(e.x, e.y) && eval(e.y) != 0 ==> res == divide(eval(e.x), eval(e.y))
    ensures e == Mod(e.x, e.y) && eval(e.y) != 0 ==> res == mod(eval(e.x), eval(e.y))
{
    match e { 
        case Literal(l: int) => e.l
        case Plus(x: Exp, y: Exp) => plus(eval(x), eval(y))
        case Minus(x: Exp, y: Exp) => minus(eval(x), eval(y))
        case Times(x: Exp, y: Exp) => times(eval(x), eval(y))
        case Divide(x: Exp, y: Exp) => divide(eval(x), eval(y))
        case Mod(x: Exp, y: Exp) => mod(eval(x), eval(y))
    }
}

method test() {
    var p := Times(3, 5);
    var r := eval(p);
    assert r == 15;
}
