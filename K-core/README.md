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
	
	
`轉換成graphx中的pregel實做: `
在graphx中的pregel API 是以邊為單位逐一造訪，為了做出如論文中pseudo code的實做，在逐一檢查邊的時候，同時檢查邊所屬的兩點是否符合K-core的條件，只要不符合及刪除該點，在刪除點的同時，所屬的邊也同時刪出，但是在graphx的pregel API 中，無法刪除邊，所以為了我將只要任何一個點被刪除的邊都判斷為已被刪除。之後每個回不斷把點刪除，直到沒有可以刪除的點為止。

`vprog`: each vertex attribute minus msgDgree
// 每一個vertex的attr為該個點的degree
//msgDegree為當回合對於該點所被刪去的邊的數目
//當回合若一個vertex的degree被刪除光了 則attr歸零
//為了防止邊的重複刪除 ，下回合起 vertex的degree 固定為-1
              
               
	vertexProgram(id: VertexId, attr: Int, msgDegree: Int): Int = {
	
		      val degree = attr - msgDegree
		      //degree為每個點被刪去的邊數 
		      //attr為原來每個點所連的邊數
		      //只要一個點的degree(attr）小於K 及刪除點
		      if (degree > 0 && degree < coreNumber) 0
			      //只要一個點所剩的邊數小於K 則此點的attr設為    零 視為已被刪除
		      else if (degree <= 0) -1
		      //停止對dttr 減去msgDegree
		      
                      //他已經被減為0了，但是有被減的情況下不能算在當回合被刪除的邊,所以用-1紀錄
                      else degree
		    }

`send message`:  send the message that the the edge was deleted
//因為Pregel api無法刪除邊，所以只要一個點被刪除的編輯視為已被刪除，並送出message "1" 紀錄
	
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

