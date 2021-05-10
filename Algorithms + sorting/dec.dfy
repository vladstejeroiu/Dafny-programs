method A(x: nat, y: nat)
    decreases x, y, 1
{
    B(x, y);
}

method B(x: nat, y: nat) 
    decreases x, y, 0
{
    if x > 0 && y > 0 {A(x - 1,y - 1);}
}