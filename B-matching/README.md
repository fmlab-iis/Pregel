#### Introduction

***

The B-Matching problem is used to build a “featured item” component for social-media applications. For example, [flickr](https://www.flickr.com) displays photos to users when they enter their personal pages, while [Yahoo!](https://www.yahoo.com) Answers displays questions that are still open for answering.

We associate a relevance score to each potential match of an item `t` to a user `u`. This score can be seen as the *weight* of the edge (t,u) of the bipartite graph between items and users. 

For each item `t` and each user `u` we also consider constraints on the maximum number of edges that `t` and `u` can participate in the matching. The goal is to find a matching that satisfies all *capacity* constraints and maximizes the total weight of the edges in the matching. 


####Problem Define

***

We are given an undirected bipartite graph `G = (T,C,E)`.
 
 `T` represents a set of items and `C` represents a set of consumers, a weight function `w : E → R+`, as well as a capacity function `b : T ∪ C → N`. 
 
 A B-matching in `G` is a subset of `E` such that for each node `v` in `T ∪ C` at most `b(v)` edges incident to `v` are in the matching. 
 
 We wish to find a B-matching of maximum weight.



####GreedyMR Algorithm

***

	while E is non empty do 
		for all v ∈ V in parallel do
		
			Let Lv be the set of b(v) edges incident to v with maximum weight;
			Let F be Lv ∩ LU where U is the set f vertexes sharing an edge with v; 
			
			Update M ← M ∪ F;
			Update E ← E \ F;
			Update b(v) ← b(v) − bF(v);
			
			If b(v) = 0 remove v from V and remove all edges incident to v from E;
			
		end for 
		
	end while 
	return M;
	
####Initial Graph

***

![mineInitialGraph](http://i.imgur.com/MVrCr2M.png)
We model the vertices to have property of type (`Int`, `Set[Edge[Int]]`, `Set[Edge[Int]]`) which store the value of `capacity`, `Lv`, `M`.

( Let `Lv` be the set of edges incident to `v` with maximum weight, `M` be the picked Edges.) 

Since edges do have property, we set an `Int` property to the edges in order to store the weight. 

So, our final graph will have the type `Graph`[`(Int, Set[Edge[Int]], Set[Edge[Int]])`, `Int`]. 



####Pregel Design

***

`initialMsg` : A empty set of edges.

`vprog` : 

	Input  (vertexId: VertexId, vertexAttr: (Int, Set[Edge[Int]], Set[Edge[Int]]), message: Set[Edge[Int]])
	Output (Int, Set[Edge[Int]], Set[Edge[Int]])
	
	if (Capacity equals 0 || message received is null) {
      return (vertexAttr)
    }
    else {
      intersection = message ∩ vertexAttr._2
      return (vertexAttr._1 - intersection.size, 
      value._2 / intersection, value._3 ∪ intersection)
    }

		


`sendMsg` :


	Input  (triplet: EdgeTriplet[(Int, Set[Edge[Int]], Set[Edge[Int]]), Int])
	Output (Iterator[(VertexId, Set[Edge[Int]])])

    if (Source vertex capacity || Destination vertex capacity == 0)
      Iterator.empty
    else {
      val set_s = triplet.srcAttr._2
      val set_d = triplet.dstAttr._2
      
      //Sends two ways
      Iterator ((triplet.dstId, set_s), (triplet.srcId, set_d) )
     }


`mergeMsg` :

	Input  (msg1: Set[Edge[Int]], msg2: Set[Edge[Int]])
	Output (Set[Edge[Int]])

	return msg1 ∪ msg2
    

#### Result

***

![Result](http://i.imgur.com/d9nYIjl.png)


![Result in graph](http://i.imgur.com/APV3St4.png)

Since the GreedyMR Algorithm is desgined to compute parallelly, Pregel works apparently. 


