
## Goal

There is a Java implementation of the bundle closure algorithm here:
https://github.com/opencaesar/owl-tools/tree/master/owl-close-world

Can we specify this bundle closure algorithm in Dafny and extract from it a Java program?

Specifying this algorithm in Dafny involves verifying Dafny methods to compute the following:
- Testing whether a graph is acyclic or not.
  Raise an exception if the graph is cyclic.
- For an acyclic graph, test whether a node is a root of a tree or not.
- For an acyclic graph, calculate its transitive reduction per https://en.wikipedia.org/wiki/Transitive_reduction


