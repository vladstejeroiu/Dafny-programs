abstract module Interface {
  class Node {
    var next: set<Node>;
  }

  predicate graph(G:set<Node>)
    reads G

  // Path(G, x,y,p) means that p is a sequence starting with x, ending with y such
  // that forall i :: 0 <= i < |p|-1 ==> p[i+1] in p[i].next
  predicate Path(G: set<Node>,x:Node,y:Node,p:seq<Node>)
    reads G, p
    requires graph(G)

  // function Next(G: set<Node>, ns: set<Node>): (rs: set<Node>)
  //   reads G
  //   requires graph(G)
  //   requires forall n :: n in ns ==> n in G
  //   ensures forall r :: r in rs ==> r in G && exists n :: n in ns && r in n.next

  // Acyclic(G) means that forall n :: n in G ==> AcyclicFrom(G, {n}, G-{n})
  predicate Acyclic(G: set<Node>)
    reads G
    requires graph(G)

  // AcyclicFrom(G, ns, rs) means that all the next nodes from ns are not in rs
  // and that this also holds recursively when adding ns' next nodes to ns and removing ns' next nodes from rs.
  predicate AcyclicFrom(G: set<Node>, ns: set<Node>, rs: set<Node>)
    reads G
    requires graph(G)
    requires forall n :: n in ns ==> n in G
    requires forall r :: r in rs ==> r in G 
    requires ns !! rs
    requires forall n :: n in ns ==> forall m :: m in n.next ==> m !in ns
    decreases |rs|
    
  // foldNext(G, ns) unions all next nodes for all nodes in ns.
  method foldNext(G: set<Node>, ns: set<Node>) returns (ms: set<Node>)
    requires graph(G)
    requires forall n :: n in ns ==> n in G
    ensures forall m :: m in ms ==> exists n :: n in ns && m in n.next
    decreases ns

}