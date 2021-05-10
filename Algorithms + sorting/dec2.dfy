method A(x: nat, y: nat)
    decreases x + y, 1
{
    if y > 2 {B(x + 2, y - 2);}
}

method B(x: nat, y: nat) 
    decreases x + y, 0
{
    if x > 2 {A(x - 2,y + 1);}
}