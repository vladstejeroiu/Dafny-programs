include "Interface.dfy"
include "Utils.dfy"

module Implementation refines Interface {
  import opened Utils

  predicate graph(G:set<Node>)
  { forall m :: m in G ==> forall n :: n in m.next ==> n in G }

  predicate Path(G: set<Node>,x:Node,y:Node,p:seq<Node>)
  { |p| > 0 && 
    p[0] == x && 
    p[|p|-1] == y && 
    (forall i :: 0 <= i && i < |p|-1 ==> p[i] in G) &&
    (forall i :: 0 <= i && i < |p|-1 ==> p[i+1] in p[i].next)
  }

  predicate Acyclic(G: set<Node>)
  {
    forall u :: u in G ==> AcyclicFrom(G, {}, G - {u})
  }
  
  predicate AcyclicFrom(G: set<Node>, ns: set<Node>, rs: set<Node>)
  {
    forall n :: n in ns ==> forall m :: m in n.next ==> m !in rs && |rs - {m}| < |rs| && AcyclicFrom(G, ns + {m}, rs - {m})
  }

  // function ReachableFrom(ns: seq<Node>, acc: set<Node>): set<Node>
  //   decreases ns
  // {
  //   if |ns| == 0 then {
  //     acc
  //   } else {
  //     ReachableFrom(ns[1..] + Utils.ToSequence(ns[0].next), acc + {ns[0]} + ns[0].next)
  //   }
  // }

  method {:tailrecursive true} Expand(G: set<Node>, ns: seq<Node>, acc: set<Node>, R:(Node, Node) -> bool, mayVisit: set<Node>) returns (s: set<Node>)
    requires Utils.IsTotalOrder(R)
    requires graph(G)
    requires forall n :: n in ns ==> n in G
    requires forall a :: a in acc ==> a in G
    requires forall v :: v in mayVisit ==> v in G
    ensures forall x :: x in s ==> x in G
    decreases mayVisit
  {
    if |ns| == 0 {
      s := acc;
    } else {
      var m : Node := ns[0];
      var ms : set<Node> := m.next - mayVisit;
      var mn : seq<Node> := Utils.SetToSequence(ms, R);
      var remaining : set<Node> := mayVisit - {m} - ms;
      assert remaining < mayVisit;
      s := Expand(G, ns[1..] + mn, acc + {ns[0]} + ns[0].next, R, remaining);
    }
  }

  method foldNext(G: set<Node>, ns: set<Node>) returns (ms: set<Node>)
  {
    if ns == {} {
      ms := {};
    } else {
      var n :| n in ns;
      var r := foldNext(G, ns - {n});
      ms := n.next + r;
    }
  }

  // method isTree(G: set<Node>, n: Node) returns (p: bool)
  //   requires Acyclic(G)
  //   requires n in G
  // {
  //   var ns := foldNext(G, {n});
  //   ts := {n} + ns;
  // }
}