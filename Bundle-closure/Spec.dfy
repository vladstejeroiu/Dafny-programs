include "Interface.dfy"

abstract module Spec {
  import I : Interface

  // method acyclicFrom(G: set<Node>, ns: set<Node>, rs: set<Node>) returns (a: bool)
  //   requires graph(G)
  //   requires forall n :: n in ns ==> n in G
  //   requires forall r :: r in rs ==> r in G 
  //   requires forall n :: n in ns ==> n !in rs
  //   requires forall r :: r in rs ==> r !in ns
  //   requires forall n :: n in ns ==> forall m :: m in n.next ==> m !in ns
  //   decreases |rs|
  // {
  //   var ms := ns + {m :: m in }
  //   a := forall n :: n in ns ==> forall m :: m in n.next ==> m !in rs && |rs - {m}| < |rs| && acyclicFrom(G, ns + {m}, rs - {m});
  // }

}