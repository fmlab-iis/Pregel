import org.apache.spark._
import org.apache.spark.graphx._
import org.apache.spark.rdd.RDD
import org.apache.log4j.Logger
import org.apache.log4j.Level

//Build a Bipartite Graph
object AuctionProblem{
  def main(args: Array[String]) {
    Logger.getLogger("org").setLevel(Level.OFF)
    Logger.getLogger("akka").setLevel(Level.OFF)
    class VertexProperty()
    case class PersonVD(assignedObj: org.apache.spark.graphx.VertexId, bid: Float) extends VertexProperty
    case class ObjectVD( owner: org.apache.spark.graphx.VertexId,  price: Float) extends VertexProperty

    def PersonLineParser(line: String): (VertexId, VertexProperty) = {
      (line.toLong, PersonVD(-1L, 0f))
    }
    def ObjectLineParser(line: String): (VertexId, VertexProperty) ={
      (line.toLong, ObjectVD(-1L, 0f))
    }
    def EdgeParser(line: String): Edge[Integer]={
      val txt = line.split(",")
      new Edge(txt(0).toLong, txt(1).toLong, txt(2).toInt)
    }
    def PersonSelfEdgeParser(line: String): Edge[Integer]={
      val txt = line.split(",")
      new Edge(txt(0).toLong, txt(1).toLong, 0)
    }
    val conf = new SparkConf().setAppName("AuctionProblem")
    val sc = new SparkContext(conf)

    val personV = sc.textFile("PersonVertex.csv").map(PersonLineParser)
    val N = personV.count()
    val objectV = sc.textFile("ObjectVertex.csv").map(ObjectLineParser)
    val EdgeRDD = sc.textFile("Edge.csv").map(EdgeParser)
    val selfEdgeRDD = sc.textFile("SelfPersonEdge.csv").map(PersonSelfEdgeParser)
    val graph = Graph(VertexRDD(personV ++ objectV), EdgeRDD++selfEdgeRDD )

   // graph.edges.collect.foreach(println(_))

    val e = 1

    val iteration = (graph.edges.reduce((a, b) => if(a.attr > b.attr) a else b).attr.toDouble / e).toInt
    type Message = (VertexId, Float, Float, Byte)
    def vprog(id: VertexId, vd: VertexProperty,msg: Message ): VertexProperty = {
      //println("This is Vprog")
      //val e = 0.0005f
      vd match {
        case PersonVD(assignedObj: VertexId, bid: Float)=> {
          //println("This is PersonVD")
          if(msg._4 == 0){
            //Decide bid
           // println(id + " decide to bid object " + msg._1 + " with best price " + msg._2 + " second price " + msg._3 )
            PersonVD(msg._1, msg._2 - msg._3 + e)
          }else if(msg._4 == -1){
           // println("Person " + id + " receive an empty msg")
            PersonVD(-2L, -2f)
          }else{
            //msg._4 == 2
            //println("msg._4 is 2 and Person " + id + "'s assign is " + msg._1 )
            PersonVD(msg._1, -1)
          }
        }
        case ObjectVD(owner: VertexId, price: Float) => {
          //println("This is ObjectVD")
          if (msg._4 == 1.toByte) {
            //println("Object " + id + "'s owner is " + msg._1 + " and its price is now " + msg._2)
            ObjectVD(msg._1, msg._2)
          }else {
            //initial
            //println("Object ini")
            ObjectVD(-1L, 0f)
          }
        }
        case _ =>{
          //println("Debug")
          ObjectVD(-9999L, -9f)
        }
      }
    }//vprog end

    def sendmsg(edge :EdgeTriplet[VertexProperty, Integer]): Iterator[(VertexId, Message)] = {
      (edge.srcAttr, edge.dstAttr) match {
        case (PersonVD(assignedObj: VertexId, bid: Float), ObjectVD(owner: VertexId, price: Float)) => {
          if(assignedObj == -1L && bid == -1f){
            //unassigned and wait price
           // println(edge.dstId + " send its value" + (edge.attr - price) + " to " + edge.srcId)
            Iterator((edge.srcId, (edge.dstId, edge.attr - price, 0f, 0.toByte)))
          }else if(assignedObj == -2L && bid == -2f){
            //wait assign
            if(owner == edge.srcId){
            // println("Person " + edge.srcId + " get Object " + edge.dstId)
              Iterator((edge.srcId, (edge.dstId, 0f,0f,2.toByte)))
            }else Iterator.empty
          }else if(assignedObj > 0L && bid >=0f ){
            if(edge.dstId == assignedObj){
              //println(edge.srcId + " send bid " + bid + " to " + edge.dstId)
              Iterator((edge.dstId, (edge.srcId, bid+price, 0f, 1)))
            }else{
              Iterator.empty
            }
          }else{
            if(assignedObj == edge.dstId && owner != edge.srcId){
              //lost object
             // println("LOST OBJ")
              Iterator((edge.srcId, (-1L, 0f, 0f, 2.toByte )))
            }else{
              Iterator.empty
            }
          }
        }
        case (PersonVD(p1Assign: VertexId, p1Bid: Float), PersonVD(p2Assign: VertexId, p2Bid: Float)) =>{
          if(p1Assign == -2L && p2Assign == -2L){
            //println("Person " + edge.srcId + " receive an empty assign msg")
            Iterator((edge.srcId, (-1L, 0f, 0f, 2.toByte)))
          }else if(p1Assign > 0L && p2Assign > 0L && p1Bid != -1f && p2Bid != -1f){
            //println(edge.srcId + " send empty msg to " + edge.dstId)
            Iterator((edge.srcId, (0L, 0f,0f, -1.toByte)))
          }else{
            Iterator.empty
          }
        }
      }

    }//sendmsg end

    def mergeMsg(a: Message, b: Message) : Message = {
      //println("This is Merge")
      if(a._4 == 0 && b._4 == 0){
        //value msg
        if(a._2 > b._2){
          if(a._3 > b._2 ){
            (a._1, a._2 , a._3, 0 )
          }else{
            (a._1, a._2 , b._2 , 0)
          }
        }else{
          if(b._3 > a._2){
            (b._1 , b._2 , b._3, 0 )
          }else{
            (b._1, b._2 , a._2 , 0 )
          }
        }
      }else if(a._4 == -1 && b._4 == -1){
        //println("empty msg")
        (0, 0, 0 , -1)
      }else if(a._4 == 1.toByte && b._4 == 1.toByte){
        //println("RUN HERE" + a._1 + " " + a._2 + " "+ b._1 + " " + b._2)
        if(a._2 >= b._2){
          (a._1 , a._2 , 0f , 1.toByte)
        }else{
          (b._1 , b._2 , 0f , 1.toByte)
        }
      }else if(a._4 == 2 && b._4 == 2){
        if(a._1 >= b._1){
          (a._1 , 0, 0, 2)
        }else{
          (b._1, 0, 0, 2)
        }
      }else{
       println("RUN==")
        (a._1, a._2 , a._3 , a._4)
      }
    }//mergeMsg end

    val resultGraph = graph.pregel((-1.asInstanceOf[VertexId],-1f,-1f, 2.toByte), iteration)(vprog, sendmsg, mergeMsg)
   // println(resultGraph.vertices.collect.mkString("\n"))
    //println(resultGraph.vertices.filter(a => a._2.isInstanceOf[PersonVD]).map(a => (a._1, a._2.asInstanceOf[PersonVD].assignedObj)).collect().mkString("\n"))
    println("Matching pairs are \n" +
      resultGraph.triplets
        .filter((edgeT) => if(edgeT.srcAttr.asInstanceOf[PersonVD].assignedObj == edgeT.dstId) true else false)
        .map(edgeT => (edgeT.srcId,edgeT.dstId,edgeT.attr,edgeT.dstAttr.asInstanceOf[ObjectVD].price))
        .collect().mkString("\n"))


    println("Maximum is " +
      resultGraph.triplets
      .filter((edgeT) => if(edgeT.srcAttr.asInstanceOf[PersonVD].assignedObj == edgeT.dstId) true else false)
      .map(edgeT => edgeT.attr)
      .reduce((a,b)=> a+b))
  }
}
