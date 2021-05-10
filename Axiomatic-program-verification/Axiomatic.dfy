/*
Axiomatic semantics is an approach based on mathematical logic for proving the correctness of computer programs. 
It is closely related to Hoare logic. 
Axiomatic semantics define the meaning of a command in a program by describing its effect on assertions about the program state.

This repo is an example of Dafny Axiomatic Program Verification. 

This code ensures that given:

datatype Tree<T> = Leaf | Node(Tree<T>, Tree<T>, T)
datatype List<T> = Nil | Cons(T, List<T>)

treeContains(tree, element) <==> listContains(flatten(tree), element)

by using dafny programming language.
*/

datatype Tree<T> = Leaf | Node(Tree<T>, Tree<T>, T)
datatype List<T> = Nil | Cons(T, List<T>)

function flatten<T>(tree:Tree<T>):List<T>

{
	match tree
    case Leaf => Nil
    case Node(l_tree,r_tree,v) => Cons(v,append(flatten(l_tree),flatten(r_tree)))

}

function append<T>(xs:List<T>, ys:List<T>):List<T>
{
	match xs
    case Nil => ys
    case Cons(x,xs') => Cons(x, append(xs',ys))
}

function treeContains<T(==)>(tree:Tree<T>, element:T):bool
{
    match tree
    case Leaf => false
    case Node(l_tree, r_tree, v) => treeContains(l_tree,element) || treeContains(r_tree,element) || (v == element) 
}

function listContains<T(==)>(xs:List<T>, element:T):bool
{
	match xs
    case Nil => false
    case Cons(x,xs') => (x == element) || listContains(xs', element)
}

lemma memberOfAppend<T>(e:T, xs:List<T>, ys:List<T>)
ensures listContains(append(xs,ys),e) == ( listContains(xs,e)  ||  listContains(ys,e) )
{
    match xs
    case Nil => {}
    case Cons(x,xs') => {
       
        calc {
           listContains(append(xs,ys),e);
            == listContains(append(Cons(x,xs'),ys),e);
            == listContains(Cons(x,append(xs',ys)),e);
            == (e==x) || listContains(append(xs',ys),e);
            == { memberOfAppend(e,xs',ys); }
               (e==x) || listContains(xs',e) || listContains(ys,e);
            == listContains(Cons(x,xs'),e)  || listContains(ys,e);
            == listContains(xs,e)           || listContains(ys,e);
        }
    }
}

lemma sameElements<T>(tree:Tree<T>, element:T)
ensures treeContains(tree, element) <==> listContains(flatten(tree), element)
{
    match tree
    case Leaf => {}
    case Node (l_tree,r_tree,v) => {
        calc{treeContains(tree,element);
        == treeContains(Node (l_tree,r_tree,v),element);
        == treeContains(l_tree,element) || treeContains(r_tree,element) || (v==element);
        == {sameElements(l_tree,element);
           sameElements(r_tree,element);}
        listContains(flatten(l_tree),element) || listContains(flatten(r_tree),element) || (v==element);
        =={memberOfAppend(element,flatten(l_tree),flatten(r_tree));} 
        listContains(append(flatten(l_tree),flatten(r_tree)),element) || (v==element);
        ==listContains(Cons(v,append(flatten(l_tree),flatten(r_tree))),element);
        ==listContains(flatten(tree), element);
        }      
    }  
}
