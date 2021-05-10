// simulates the following deterministic Finite State Automaton which accepts an input string if it ends in 0
// A = ({0, 1}, {0, 1}, delta, 0, {1})
// delta(0, 0) = 1, delta(0, 1) = 0, delta(1, 0) = 1, delta(1, 1) = 0


method simulate(s: seq<int>, transitions: seq<seq<int>>, initial: int, acceptStates: set<int>) returns (endState: int)
    requires 0 <= initial < |transitions|
    requires transitions == [[1, 0], [1, 0]]
    requires acceptStates == {1}
    requires forall k :: 0 <= k < |s| ==> s[k] == 0 || s[k] == 1
    ensures |s| > 0 && s[|s|-1] == 0 ==> endState in acceptStates
    ensures |s| > 0 && s[|s| - 1] != 0 ==> endState !in acceptStates
{
    var index := 0;
    var currentState := initial;
    while index < |s| 
        invariant 0 <= index <= |s|
        invariant 0 <= currentState < |transitions|
        invariant index > 0 ==> currentState == transitions[old(currentState)][s[index  - 1]]
    {
        var c := s[index];
        currentState := transitions[currentState][c];
        index := index + 1;
    }

    endState := currentState;
}

// method Main() {
//     var endState := simulate([1, 0], [[1, 0], [1, 0]], 0, {1});
//     assert endState == 1;
    
//     print "End state is: ";
//     print endState;
//     print "\n";
// }

const a := 2;
method Main() {
  print "\n";
  print "\n";
}

method d(i: int, j: int) returns (res: int)
  requires i > 0
  requires j > 0
  ensures res == 6
{  
    return i;
}


