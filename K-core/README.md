#Introduction
***
The k-core of a graph is the subgraph in which all vertices have degree of at least k. The algorithm iteratively removes vertices with degrees less than k, and stops when there is no vertex to remove. At the end of the execution, the remaining graph represents the k-core. It is possible that the result is an empty graph.

`Pregel-like pseudo code (from "Using Prefol-like Large Scale Graph Processing Frameworks for Social Networking Analysis")`

	repeat
	  begin Superstep n
	     if Node degree < k then
	         delete node and out-edges
	     end if
	  end
	until No nodes deleted in previous superstep

`vprog`: each vertex attribute minus msgDgree

	vertexProgram(id: VertexId, attr: Int, msgDegree: Int): Int = {
		      val degree = attr - msgDegree
		      //degree為每個點要被刪去的邊數 
		      //attr為原來每個點所連的邊數
		      if (degree > 0 && degree < coreNumber) 0
			      //只要一個點所剩的邊數小於K 則此點的attr設為    零 視為已被刪除
		      else if (degree <= 0) -1
		      //停止對dttr 減去msgDegree
		      //因為每回合會減去被刪除的邊 所以用-1紀錄已經被刪 過的邊
		      else degree
		    }

`send message`:  send the message that the the edge was deleted
	
	//Message record whether the edge of vetex is deleted
    //if the edge has only one vertex ,regarding it was      //deleted
	sendMessage(edge: EdgeTriplet[Int, Int]): Iterator[(VertexId, Int)] = {
	      if (edge.dstAttr > 0 && edge.srcAttr == 0) {
	        Iterator((edge.dstId, 1), (edge.srcId, 1))
	        //要是dst存在 但src不存在 則送出msg: "1" 
	      } else if (edge.srcAttr > 0 && edge.dstAttr == 0) 
	      {
	        Iterator((edge.srcId, 1), (edge.dstId, 1))
	        //要是src存在 但dst不存在 則送出msg: "1" 
	      } else {
	        Iterator()//iterate empty
	      }
	    }
`merge`:  calculate the number of  edges deleted in current stage of each vertex

	 messageCombiner(a: Int, b: Int): Int = {a + b}
	                //count how much edges was deleted
                    //將全部要被減去的邊的數目加起來
