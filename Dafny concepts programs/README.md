
Note: The files in this repo are not meant to be self-explanatory, they're just examples which someone who already knows Dafny can use to introduce others to Dafny.
To learn Dafny on your own, the resources listed in [Dafny's README](https://github.com/dafny-lang/dafny/#read-more) and the [Dafny Wiki](https://github.com/dafny-lang/dafny/wiki) are the best places to start.


Contents:
* Functional Dafny with Algebraic Datatypes, and a small compiler: `NipkowKlein-chapter3.dfy`
* Simple inductive predicates, and exception handling syntax: `ChurchNats.dfy`
* Inductive predicates in bedrock2 postcondition style, and limitations: `Amb.dfy`
* An example where Dafny shines: Map lemmas `Maps.dfy`
* Dynamic frames: `DynamicFrames.dfy`, `Disjointness.dfy`, `WrappedCounters.dfy`, `FlyingRobots.dfy`
* Some Dafny code in practice: Base64 encoding and decoding, and a proof that encoding and then decoding yields the original string (`Base64Lib.dfy`, `Base64Use.dfy`)
* Modeling External State Correctly or How To Avoid Assuming False: `ExternalStateBad.dfy`, `ExternalStateGood.dfy`
* Some nice examples from Dafny's test suite: `BinarySearch.dfy`, `UnionFind.dfy`, `BinaryTree.dfy`