####Problem Define

***

The travelling salesman problem (TSP) asks the following question: Given a list of cities and the distances between each pair of cities, what is the shortest possible route that visits each city exactly once and returns to the origin city?
	
####Initial Graph

***

![mineInitialGraph](http://i.imgur.com/1kJ5mRY.png)

We model the vertices to have property of type (`Int`,  `Set[P]`,  `Set[P]`)which store the value of `Number of Vertices`, `Candidate Paths`, `Picked Path`, `Index of Supersteps`.

Since edges do have property, we set an `Int` property to the edges in order to store the weight.

So, our final graph will have the type `Graph`[(`Int`,  `Set[P]`,  `Set[P]`), `Int`]. 



####Pregel Design

***


`initialMsg` : 

	(Set[P]())

`vprog` : 

        for(a <- message) {
          if(The Path's length equals (Number of Vertices + 1)){
            Add the path to "Picked Paths"
          }
        }
        if(Special Case for Vertex #1 in superstep 0){
          	Add Vertex #1 to "Candidate Path"
        }else{
          	return new value
        }


`sendMsg` :

        if(SrcVertex' Candidate Path Set isn't empty) {
          for (Every Candidate Path) {
            if (DesVertex is't in the path) {
              Add DesVertex to the path, and send the path to DestVertex.
            }else if(the candidate path has visited all vertices, and DesVertex is #1){
              Add DesVertex to the path, and send the path to DestVertex.
            }
          }
        }
        
        Repeat again for DesVertex => SrcVertex


`mergeMsg` :
	
	msg1 ++ msg2
    

#### Result

***

![Result](http://i.imgur.com/cjWzlHS.png)


![Result in graph](http://i.imgur.com/g7ylXg1.png)



