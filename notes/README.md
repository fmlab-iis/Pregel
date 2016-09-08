# Pregel notes

## Code and proofs

### Pregel-graph-coloring

- Proof (Pseudo) ([Dafny](https://github.com/fmlab-iis/Pregel/blob/master/notes/pregel-graph-coloring-nondet.dfy))

### Pregel-connected-components

- Proof ([Pseudo](https://stackedit.io/editor#!provider=couchdb&id=8DhEhGClhi5a4RR0FWenfjDD)) ([Dafny](https://github.com/fmlab-iis/Pregel/blob/master/notes/pregel-graph-connected-components.dfy))

### Pregel-shortest-paths 
- Proof ([Pseudo](https://stackedit.io/editor#!provider=couchdb&id=rySR3YsgK6PXjmv1w2Gw1TfT)) ([Dafny](https://github.com/fmlab-iis/Pregel/blob/master/notes/pregel-graph-shortest-paths-nondet-v3.dfy))

## Active set in Pregel

The GraphX computation framework constructs a realization of Pregel based on the Gather-Apply-Scatter (GAS) pattern. GAS breaks down the computation of vertex program into purely edge-parallel and vertex-parallel stages called *gather*, *apply* and *scatter*. In the gather stage, an associative and commutative operator `mergeMsg` is used to reduce the inbound messages of a vertex. In the apply stage, a function `vprog` updates the value of a vertex based on the reduced inbound message. In the scatter stage, a function `sendMsg` computes and sends messages along each edge. Note, unlike more standard implementations of Pregel, GraphX does not allow modification of graph topology and edge attribute during execution. Besides, message communication is only allowed between the neighboring vertices. These restrictions are imposed so as to increase parallelism and enable more system optimizations within GraphX.

In contrast to the original Pregel abstraction where vertices are deactivated through voting to halt, GraphX Pregel does not provide operations for explicit state transition. Instead, it avoids executing the `sendMsg` function on the edges where neither side received a message. These edges will remain skipped until their endpoints receive a message again. Hence, an edge in GraphX Pregel is a two-state machine that is deactivated if it does not receive any message and reactivated after it receives a message. GraphX will execute `sendMsg` only on the activated edges.

In practice, GraphX decides whether an edge is activated or not by bookkeeping the set of vertices that received messages from the last superstep, called the *active set*. An edge is activated iff it is incident to a vertex in the active set. The bookkeeping mechanism however increases the complexity and difficulty for us to reason about the behaviors of a Pregel program. Instead, consider a modified version of the GraphX Pregel where `sendMsg` is executed on all edge in each superstep. It turns out that the semantics of the modified version coincides with the original one under some conditions:  

*Fact.* The bookkeeping mechanism in GraphX Pregel is transparent if the `sendMsg` function only depends on the edge triplet, namely, the edge attribute, the source vertex, and the destination vertex.

*Proof.* Suppose we have two GraphX frameworks, so that one of them executes `sendMsg` only on activated edges and the other executes `sendMsg` on all edges. Without loss of generality, assume the `vprog` function to be deterministic. We will show that, given the same initial message and the same input graph, a Pregel program produces the same output graph in both frameworks on termination. The proof is done by induction on the number of the supersteps taken by the program.<br />
*Superstep 0.* Since `vprog` is deterministic and the initial message is sent to all vertices without executing `sendMsg`, the program produces the same graph after the first superstep in both frameworks.<br />
*Superstep n+1.* Suppose the program produces the same graph after the *n*th superstep. Consider an edge *e* in the (*n+1*)-th superstep. If *e* is active, then the `sendMsg` function behaves the same on it in both frameworks. If *e* is inactive, then two facts about its endpoints hold in the last superstep: i) they did not receive any message from *e*, and ii) they did not change values. Since edge attribute is immutable and `sendMsg` only depends on the edge triplet, `sendMsg` would send no messages along *e* even if it is executed on *e*. Hence, the `sendMsg` function sends the same messages to the same vertex in both frameworks. Since `mergeMsg` is associative and commutative, each vertex receives the same reduced inbound message in both frameworks. Finally, since `vprog` is deterministic, the program produces the same graph in both frameworks after the (*n+1*)-th superstep. This concludes our proof.

Note that the condition for the above fact to hold is automatically satisfied if the user-defined functions are pure. Hence, we can safely assume that all edges are activated when we are simulating or reasoning about a pure Pregel program in GraphX. 