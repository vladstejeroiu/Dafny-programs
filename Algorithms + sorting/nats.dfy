
datatype natr = Zero | Succ(natr)

// --------- Predicates --------- //

predicate Odd(x: natr)
{
    match x
        case Zero => false
        case Succ(Zero) => true
        case Succ(x') => Odd(x')
}

predicate Even(x: natr)
{
    match x
        case Zero => true
        case Succ(Zero) => false
        case Succ(x') => Even(x')
}

// --------- Lemmas --------- //

ghost method prop_add_Zero(x: natr)
    ensures add(x, Zero) == x;
{ }

ghost method prop_add_Succ(x: natr, y: natr)
    ensures Succ(add(x, y)) == add(x, Succ(y))
{ }

ghost method prop_add_comm(x: natr, y: natr)
    ensures add(x, y) == add(y, x)
{
    // Prueba por induccion de x
    match x {
        // Caso base
        case Zero =>
            calc {
                add(Zero, y);
            ==  { prop_add_Zero(y); }
                add(y, Zero);
            }
        // Paso inductivo
        case Succ(x') =>
            calc {
                add(x, y);
            ==  { prop_add_Succ(y, x'); }
                add(y, Succ(x'));
            }
    }
}

// --------- Functions --------- //

function add(x: natr, y: natr) : natr
{
    match x
        case Zero => y
        case Succ(x') => Succ(add(x', y))
}

// --------- Program --------- //

method Main() {

    // Declaration of variables
    var nZero := Zero;
    var nOne := Succ(nZero);
    var nTwo := Succ(nOne);
    var nThree := Succ(nTwo);
    var nFour := Succ(nThree);
    var nFive := Succ(nFour);

    // TEST: prop_add_Zero
    assert(add(Zero, nThree) == nThree);
    assert(add(nThree, Zero) == nThree);
    
    // TEST: prop_add_comm
    assert(add(nThree, Zero) == add(Zero, nThree));

    // TEST: add
    assert(add(nTwo, nThree) == nFive);
}
