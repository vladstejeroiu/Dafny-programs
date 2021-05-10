// Copyright Jaco van de Pol, 21 january 2015, J.C.vandePol@utwente.nl
// Formal Methods and Tools, CTIT, University of Twente, The Netherlands

// Jaco van de Pol, Automated verification of Nested DFS. 
// In: FMICS 2015, Oslo, pp. 181-197, Springer LNCS 9128.
// http://dx.doi.org/10.1007/978-3-319-19458-5_12

// Updated for Dafny 3.0.0 pre-release 1 by N. Rouquette

datatype Color = white | cyan | blue | pink | red

class Node {
  var next: seq<Node>;
  var accepting: bool;
  var color1: Color;
  var color2: Color;
}

class NDFS {
  ghost var G: set<Node>;

  predicate graph(G:set<Node>)
    reads G;
  { forall m :: m in G ==> forall n :: n in m.next ==> n in G }

  predicate types(G:set<Node>)
    reads G; requires graph(G);
  { forall m :: m in G ==> 
        m.color1 in {white,cyan,blue}  
    &&  m.color2 in {white,pink,red}}

  function Cyan(G:set<Node>): set<Node>
    reads G; requires graph(G);
  { set n | n in G && n.color1 == cyan :: n }

  function Blue(G:set<Node>): set<Node>
    reads G; requires graph(G);
  { set n | n in G && n.color1 == blue :: n }

  function Pink(G:set<Node>): set<Node>
    reads G; requires graph(G);
  { set n | n in G && n.color2 == pink :: n }

  function Red(G:set<Node>): set<Node>
    reads G; requires graph(G);
  { set n | n in G && n.color2 == red :: n }

  predicate Next(G:set<Node>,X:set<Node>,Y:set<Node>)
    reads G; requires graph(G);
  { forall n,i :: n in G && 0 <= i < |n.next| && 
        n in X ==> n.next[i] in Y
  }

  function Path(G:set<Node>,x:Node,y:Node,p:seq<Node>):bool
    reads G; requires graph(G); requires x in G; requires y in G; requires forall i :: i in p ==> i in G;
  { |p| > 0 && p[0] == x && p[|p|-1] == y
    && forall i :: 0 <= i < |p|-1 ==> p[i] in G && p[i+1] in p[i].next }

  function Cycle(G:set<Node>,x:Node,y:Node,p:seq<Node>,q:seq<Node>):bool
    reads G; requires graph(G);
  {  Path(G,x,y,p) && Path(G,y,y,q) && |q| > 1 && y.accepting }

  function KeyInvariant(G:set<Node>):bool
    reads G
    requires graph(G)
  { 
    forall s :: s in Blue(G) && s.accepting ==> 
      // TODO: How to fix this?
      // a quantifier involved in a function definition is not allowed to depend on 
      // the set of allocated references; Dafny's heuristics can't figure out a bound for the values of 'p'
      !exists p :: |p| > 1 && Path(G,s,s,p) 
  }

  function NoPath(G:set<Node>,s:Node,t:Node,p:seq<Node>):bool
    reads G; requires graph(G);
    requires Next(G,Red(G),Red(G));
    requires Next(G,Red(G),G - Cyan(G));
    requires s in Red(G);
    requires t in Cyan(G);
    ensures NoPath(G,s,t,p);
    ensures |p| > 1 ==> !Path(G,s,t,p);
  { |p| > 1 && p[0] == s && p[1] in p[0].next ==> NoPath(G,p[1],t,p[1..]) }

  function NoCycle(G:set<Node>,root:Node,s:Node,p:seq<Node>,q:seq<Node>):bool
    reads G; requires graph(G);
    requires root in Blue(G);
    requires Next(G,Blue(G),Blue(G));
    requires KeyInvariant(G);
    ensures !Cycle(G,root,s,p,q);
  { |p| > 1 && p[0] == root && p[1] in p[0].next ==> NoCycle(G,p[1],s,p[1..],q) }

  lemma NextCyan(G:set<Node>,s:Node,t:Node)
    requires graph(G);
    requires s in G;
    requires t in s.next;
    requires forall c :: c in Cyan(G) ==> exists q :: Path(G,c,s,q);
    ensures  forall c :: c in Cyan(G) ==> exists q :: Path(G,c,t,q);
  { assert forall c,p :: Path(G,c,s,p) ==> Path(G,c,t,p+[t]); }

  lemma CycleFoundHere(G:set<Node>,s:Node)
    requires graph(G);
    requires s in G;
    requires s.accepting;
    requires exists c,p :: c in Cyan(G) && Path(G,s,c,p) && |p|>1;
    requires forall c :: c in Cyan(G) ==> exists q :: Path(G,c,s,q);
    ensures exists p,q :: Cycle(G,s,s,p,q);
  { assert exists c,p,q :: c in Cyan(G) && |p|>1 && Path(G,s,c,p) && Path(G,c,s,q);
    assert forall c,p,q :: Path(G,s,c,p) && Path(G,c,s,q) ==> Path(G,s,s,p+q[1..]);
    assert forall q :: |q| > 1 && Path(G,s,s,q) ==> Cycle(G,s,s,[s],q);
  } // this was very hard to prove and rather sensitive...

  method ndfs(root:Node) returns (found:bool)
    requires graph(G);
    requires root in G;
    requires forall s :: s in G ==> s.color1 == s.color2 == white;
    modifies G`color1, G`color2;
    ensures found ==> (exists a,p,q :: Cycle(G,root,a,p,q));  // soundness
    ensures (exists s,p,q :: Cycle(G,root,s,p,q)) ==> found;  // completeness
  { found := dfsblue(root);
    assert !found ==> forall s,p,q :: 
      NoCycle(G,root,s,p,q) ==> !Cycle(G,root,s,p,q);
  }

  method dfsblue(s:Node) returns (found:bool)
    requires s in G;
    requires graph(G);
    requires types(G);
    requires s.color1 == white;
    requires Next(G,Blue(G),Blue(G) + Cyan(G));
    requires Next(G,Red(G),Red(G) + Pink(G));
    requires Pink(G) == {};
    requires Red(G) <= Blue(G);
    requires KeyInvariant(G);
    requires forall c:: c in Cyan(G) ==> exists p :: Path(G,c,s,p);
    modifies G`color1, G`color2;
    decreases G - Cyan(G);
    ensures types(G);
    ensures old(Blue(G)) <= Blue(G);
    ensures Next(G,Blue(G),Blue(G) + Cyan(G));
    ensures Next(G,Red(G),Red(G) + Pink(G));
    ensures !found ==> s in Blue(G);
    ensures !found ==> old(Cyan(G)) == Cyan(G);
    ensures !found ==> Pink(G) == {};
    ensures !found ==> Red(G) <= Blue(G);
    ensures found ==> (exists a,p,q :: Cycle(G,s,a,p,q));
    ensures KeyInvariant(G);

  { s.color1 := cyan;
    assert Path(G,s,s,[s]);
    var i := 0;
    while (i < |s.next|) 
    invariant types(G);
    invariant Cyan(G) == old(Cyan(G)) + {s};
    invariant Pink(G) == {};
    invariant i <= |s.next|;
    invariant forall j :: 0 <= j < i ==> s.next[j] in Blue(G) + Cyan(G);
    invariant old(Blue(G)) <= Blue(G);
    invariant Next(G,Blue(G),Blue(G) + Cyan(G));
    invariant Next(G,Red(G),Red(G) + Pink(G));
    invariant Red(G) <= Blue(G);
    invariant KeyInvariant(G);

    { var t := s.next[i];
      i := i+1;
      if (t.color1 == white) 
      { NextCyan(G,s,t);
        found := dfsblue(t); 
        if (found) { 
          assert forall a,p,q :: Cycle(G,t,a,p,q) ==> Cycle(G,s,a,[s]+p,q);
          return; 
        }
      }
    }
    if (s.accepting)
    { assert s !in Pink(G);
      found := dfsred(s,s);
      if (found) { 
        CycleFoundHere(G,s);
        return; 
      }
      assert forall p :: NoPath(G,s,s,p);
    }
    s.color1 := blue;
    return false;
  }

  method dfsred(s:Node, ghost root:Node) returns (found:bool)
    requires graph(G); 
    requires types(G);
    requires s in G;
    requires root in G;
    requires s.color2 == white;
    requires s == root || s.color1 == blue;
    requires Next(G,Blue(G) + {root},Blue(G) + Cyan(G));
    requires Next(G,Red(G),Red(G) + Pink(G));
    requires Red(G) <= Blue(G) + {root};
    requires Next(G,Red(G),G - Cyan(G));
    modifies G`color2;
    decreases G - Pink(G);
    ensures types(G);
    ensures !found ==> s in Red(G);
    ensures !found ==> old(Pink(G)) == Pink(G);
    ensures old(Red(G)) <= Red(G);
    ensures Next(G,Red(G),Red(G) + Pink(G));
    ensures Red(G) <= Blue(G) + {root};
    ensures Next(G,Red(G),G - Cyan(G));
    ensures found ==> exists p,c :: |p| > 1 && c in Cyan(G) && Path(G,s,c,p);

  { s.color2 := pink;
    var i := 0;
    while (i < |s.next|)
    invariant types(G);
    invariant old(Red(G)) <= Red(G);
    invariant i <= |s.next|;
    invariant forall j :: 0 <= j < i ==> s.next[j] in Red(G) + Pink(G);
    invariant Next(G,Red(G),Red(G) + Pink(G));
    invariant Pink(G) == old(Pink(G)) + {s};
    invariant Red(G) <= Blue(G) + {root};
    invariant Next(G,Red(G),G - Cyan(G));
    invariant forall j :: 0 <= j < i ==> s.next[j] in G - Cyan(G);

    { var t := s.next[i];
      i := i+1;
      if (t.color1 == cyan) { 
        assert Path(G,s,t,[s,t]);
        return true; 
      }
      if (t.color2 == white)
      { found := dfsred(t,root);
        if (found) { 
          assert forall p,c :: Path(G,t,c,p) ==> Path(G,s,c,[s]+p);
          return; 
        }
      }
    }
    s.color2 := red;
    return false;
  }
}