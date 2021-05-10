// A simple variant of interaction trees.
// Should form a monad and can be seen as a computation.
datatype ITree<A> =
| IOut(msg: string, void_cont: () -> ITree<A>)
| IIn(str_cont: string -> ITree<A>)
| IRet(a: A)

function IBind<A, B>(m: ITree<A>, f: A -> ITree<B>): ITree<B> 
    decreases m
{
    match m {
        case IOut(msg, void_cont) => IOut(msg, (() => IBind(void_cont(), f))) // failure to decrease termination measure
        case IIn(str_cont) => IIn(a => IBind(str_cont(a), f)) // failure to decrease termination measure
        case IRet(a) => f(a)
    }
}
