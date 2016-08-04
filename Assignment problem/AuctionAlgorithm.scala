import org.apache.spark._
import org.apache.spark.graphx._
import org.apache.spark.rdd.RDD

//Build a Bipartite Graph
trait VertexProperty
case class PersonVD(val assignedObj: org.apache.spark.graphx.VertexId, val bid: Double, val status: Int) extends VertexProperty
case class ObjectVD(val owner: org.apache.spark.graphx.VertexId, val price: Double, val status: Int) extends VertexProperty

def PersonLineParser(line: String): (VertexId, VertexProperty) = { 
    (line.toLong, PersonVD(-1L, 0.0, 0))
}
def ObjectLineParser(line: String): (VertexId, VertexProperty) ={
    (line.toLong, ObjectVD(-1L, 0.0, 0))
}
def EdgeParser(line: String): Edge[Integer]={
    val txt = line.split(",")
    new Edge(txt(0).toLong, txt(1).toLong, txt(2).toInt)
}

val personV = sc.textFile("PersonVertex.csv").map(PersonLineParser)
val objectV = sc.textFile("ObjectVertex.csv").map(ObjectLineParser)
val EdgeRDD = sc.textFile("Edge.csv").map(EdgeParser)
val graph = Graph(VertexRDD(personV ++ objectV), EdgeRDD)

//graph.vertices.collect.foreach(println(_))

val e = 0.2

val iteration = (graph.edges.reduce((a, b) => if(a.attr > b.attr) a else b).attr.toDouble / 0.2).toInt
type Message = (VertexId, Double, Double)
def vprog(id: VertexId, vd: VertexProperty,msg: Message ): VertexProperty = {
    val e = 0.2
    vd match {
    	case PersonVD(assignedObj : VertexId, bid : Double, 0) => {
    		if(msg == (0,0,0)){
    			PersonVD(assignedObj,bid,1)
    		}else{
    			if(msg != (0,0,2)){
    				PersonVD(msg._1, 0, 1)
    			}
    			else{
    				PersonVD(-1L, 0, 1)
    			}
    		}
    	}
    	case PersonVD(assignedObj : VertexId,bid : Double,1) => {
    		PersonVD(msg._1, msg._2 - msg._3 + e, 0)
    	}
    	case ObjectVD(owner : VertexId, price : Double, 0) => ObjectVD(owner, price, 1)
    	case ObjectVD(owner : VertexId, price : Double, 1) => {
    		if(msg._1 == 0) ObjectVD(owner, price, 0)
    		else ObjectVD(msg._1, msg._2, 0)
    	}
    	case _ => PersonVD(-999, -999, -999)
    }
    


}//vprog end

def sendmsg(edge :EdgeTriplet[VertexProperty, Integer]): Iterator[(VertexId, Message)] = {
	
	val personStatus : Int = edge.dstAttr.asInstanceOf[PersonVD].status
	val objectStatus : Int = edge.srcAttr.asInstanceOf[ObjectVD].status


	if(personStatus == 1){
		if(edge.dstAttr.asInstanceOf[PersonVD].assignedObj == -1){
			Iterator((edge.srcId, (edge.dstId , edge.attr - edge.srcAttr.asInstanceOf[ObjectVD].price, 0)))
		}else{
			Iterator.empty
		}
	}else if(objectStatus == 1 && personStatus == 0){
		if(edge.dstAttr.asInstanceOf[PersonVD].assignedObj == edge.dstId){
			Iterator((edge.dstId, (edge.srcId, edge.dstAttr.asInstanceOf[PersonVD].bid, 1)))
		}else{
			Iterator((edge.dstId, (0,0,1)))
		}
	}else if(objectStatus == 0 && personStatus == 0){
		if(edge.srcAttr.asInstanceOf[ObjectVD].owner != -1){
			if(edge.srcId == edge.srcAttr.asInstanceOf[ObjectVD].owner){
				Iterator((edge.srcId, (edge.dstId, 0, 2)), (edge.dstId, (0,0,2)))
			}else{
				Iterator((edge.srcId, (0,0,2)), (edge.dstId, (0,0,2)))
			}
		}else{
			Iterator((edge.dstId, (0,0,2)))
		}
	}else{
		Iterator.empty
	}
}//sendmsg end

def mergeMsg(a: Message, b: Message) : Message = {
	if(a._3 == 0 && b._3 == 0){
		if(a._2 > b._2){
			(a._1, a._2, b._2)
		}
		else{
			(b._1, b._2, a._2)
		}
	}else if(a._3 == 2 && b._3 == 2){
		if(a._1 > b._1){
			(a._1, 0, 2)
		}else{
			(b._1, 0, 2)
		}
	}else{
		if(a._2 > b._2){
			(a._1, a._2, 1)
		}else{
			(b._1, b._2, 1)
		}
	}
}//mergeMsg end

val resultGraph = graph.pregel((0.asInstanceOf[VertexId],0.0,0.0), iteration)(vprog, sendmsg, mergeMsg)
println(resultGraph.vertices.collect.mkString("\n"))

