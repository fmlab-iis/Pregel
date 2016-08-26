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

![mineInitialGraph](http://i.imgur.com/0rBd2X5.png)

We model the vertices to have property of type (`Int`, `Set[Edge[Int]]`, `Set[Edge[Int]]`, `Set[Edge[Int]]`) which store the value of `capacity`, `Candidate Edges`, `Lv`, `M`.

( Let `Lv` be the set of edges incident to `v` with maximum weight, `M` be the picked Edges.) 

Since edges do have property, we set an `Int` property to the edges in order to store the weight. 

So, our final graph will have the type `Graph`[`(Int, Set[Edge[Int]], Set[Edge[Int]], Set[Edge[Int]])`, `Int`]. 



####Pregel Design

***


`initialMsg` : 

	Set((Set[Edge[Int]](), 0))

`vprog` : 

      def vprog(vertexId: VertexId, value: (Int, Set[Edge[Int]], Set[Edge[Int]], Set[Edge[Int]]), message: Set[(Set[Edge[Int]], Int)]): (Int, Set[Edge[Int]], Set[Edge[Int]], Set[Edge[Int]]) = {
        var newValue_1 = value._1
        var newValue_2 = value._2
        var newValue_3 = value._3
        var newValue_4 = value._4
        var neededCandidateNum = 0

        for (op <- message) op._2 match{
          case 0 => {
            neededCandidateNum = value._1 - value._3.size
            newValue_3 = value._3 ++ value._2.toSeq.sortWith(_.attr > _.attr).take(neededCandidateNum).toSet
            newValue_2 = value._2 -- newValue_3
          }
          case 1 => { //Pick me
            //println("ID => "+vertexId+" received "+op._1)
            newValue_1 = newValue_1 - 1
            newValue_3 = newValue_3 -- op._1
            newValue_4 = newValue_4 ++ op._1
          }
          case 2 => { //Kill me
            newValue_2 = newValue_2 -- op._1
            newValue_3 = newValue_3 -- op._1

            neededCandidateNum = value._1 - value._3.size
            if(neededCandidateNum > 0){
              newValue_3 = newValue_3 ++ value._2.toSeq.sortWith(_.attr > _.attr).take(neededCandidateNum).toSet
              newValue_2 = newValue_2 -- newValue_3
            }
          }
          case 3 => { //I'm useless, just check
            neededCandidateNum = value._1 - value._3.size
            if(neededCandidateNum > 0){
              newValue_3 = value._3 ++ value._2.toSeq.sortWith(_.attr > _.attr).take(neededCandidateNum).toSet
              newValue_2 = value._2 -- newValue_3
              newValue_4 = value._4
            }
          }


`sendMsg` :


        if(triplet.srcAttr._2(self) || triplet.srcAttr._3(self) || triplet.dstAttr._2(self) || triplet.dstAttr._3(self)){
            if(triplet.srcAttr._1 == 0 || triplet.dstAttr._1 == 0){
              val tmp: Set[(Set[Edge[Int]], Int)] = Set((Set(self),2))
              return Iterator((triplet.dstId, tmp), (triplet.srcId, tmp))
            }
            if(triplet.srcAttr._3(self) && triplet.dstAttr._3(self)){
              val tmp: Set[(Set[Edge[Int]], Int)] = Set((Set(self),1))
              return Iterator((triplet.dstId, tmp), (triplet.srcId, tmp))
            }
        }else{
          val tmp: Set[(Set[Edge[Int]], Int)] = Set((Set(self),3))
          return Iterator((triplet.dstId, tmp), (triplet.srcId, tmp))
        }


`mergeMsg` :

	if (msg1 == null && msg2 == null) null
        else  msg1.union(msg2)
    

#### Result

***

![Result](http://i.imgur.com/d9nYIjl.png)


![Result in graph](http://i.imgur.com/yvV19w1.png)


