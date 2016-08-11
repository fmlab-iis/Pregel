import org.apache.spark._
import org.apache.spark.graphx._
import org.apache.spark.rdd.RDD

//Build a Bipartite Graph
object AuctionProblem{
  def main(args: Array[String]) {
    class VertexProperty()
    case class PersonVD(assignedObj: org.apache.spark.graphx.VertexId, bid: Double, status: Int) extends VertexProperty
    case class ObjectVD( owner: org.apache.spark.graphx.VertexId,  price: Double) extends VertexProperty

    def PersonLineParser(line: String): (VertexId, VertexProperty) = {
      (line.toLong, PersonVD(-1L, 0.0, 0))
    }
    def ObjectLineParser(line: String): (VertexId, VertexProperty) ={
      (line.toLong, ObjectVD(-1L, 0.0))
    }
    def EdgeParser(line: String): Edge[Integer]={
      val txt = line.split(",")
      new Edge(txt(0).toLong, txt(1).toLong, txt(2).toInt)
    }
    val conf = new SparkConf().setAppName("AuctionProblem")
    val sc = new SparkContext(conf)

    val personV = sc.textFile("PersonVertex.csv").map(PersonLineParser)
    val objectV = sc.textFile("ObjectVertex.csv").map(ObjectLineParser)
    val EdgeRDD = sc.textFile("Edge.csv").map(EdgeParser)
    val graph = Graph(VertexRDD(personV ++ objectV), EdgeRDD)

    //graph.vertices.collect.foreach(println(_))

    val e = 0.2

    val iteration = (graph.edges.reduce((a, b) => if(a.attr > b.attr) a else b).attr.toDouble / 50).toInt
    type Message = (VertexId, Double, Double)
    def vprog(id: VertexId, vd: VertexProperty,msg: Message ): VertexProperty = {
      val e = 0.2
      println(id + " prefer " + msg._1 + " msg._3 " +  msg._3 )
      vd match{
        case PersonVD(assignedObj: VertexId, bid: Double, 0) => {
          if (msg._1 == -1L) {
            PersonVD(-1L, 0.0, 1)
          }
          else{
            PersonVD(msg._1, 0, 1)
          }
        }
        case PersonVD(assignedObj: VertexId, bid: Double, 1) =>{
          if(msg._3 == -2){
            PersonVD(-1L, 0.0, 1)
          }
          else{
            PersonVD(msg._1, msg._2 - msg._3 + e , 2 )
          }
        }
        case PersonVD(assignedObj: VertexId, bid: Double, 2) =>{
          PersonVD(-1L, 0, 0)
        }

        case ObjectVD(owner: VertexId, price: Double) => {
          ObjectVD(msg._1, msg._2)
        }
        case _ => {
          println("Something wrong")
          PersonVD(999L, 99, 9 )
        }
      }
    }//vprog end

    def sendmsg(edge :EdgeTriplet[VertexProperty, Integer]): Iterator[(VertexId, Message)] = {
      val personStatus : Int = edge.srcAttr.asInstanceOf[PersonVD].status
      if(personStatus == 1){
        if(edge.srcAttr.asInstanceOf[PersonVD].assignedObj == -1){
         // println("Get value from " + edge.dstId + " is " + (edge.attr - edge.dstAttr.asInstanceOf[ObjectVD].price) )
          Iterator((edge.srcId, (edge.dstId, edge.attr - edge.dstAttr.asInstanceOf[ObjectVD].price, 0)))
        }else{
          if(edge.srcAttr.asInstanceOf[PersonVD].assignedObj == edge.dstId && edge.dstAttr.asInstanceOf[ObjectVD].owner != edge.srcId){
            Iterator((edge.srcId, (0L, 0.0, 2)))
          }else{
            Iterator.empty
          }
        }
      }else if(personStatus == 2){
        if(edge.dstId == edge.srcAttr.asInstanceOf[PersonVD].assignedObj){
          Iterator((edge.srcId, (0L, 0.0, -1)),(edge.dstId, (edge.srcId, edge.srcAttr.asInstanceOf[PersonVD].bid, -3)))
        }else{
          Iterator.empty
        }
      }else{
        if(edge.srcId == edge.dstAttr.asInstanceOf[ObjectVD].owner){
          Iterator((edge.srcId, (-1L, 0, -2)), (edge.srcId, (edge.dstId, 0.0, -2)))
        }else{
          Iterator((edge.srcId, (-1L, 0, -2)))
        }
      }

    }//sendmsg end

    def mergeMsg(a: Message, b: Message) : Message = {
        if(a._3 == -2 && b._3 == -2){
          if(a._1 > b._1){
            (a._1, 0, -2)
          }else{
            (b._1, 0, -2)
          }
        }else if(a._3 == -3 && b._3 == -3){
          if(a._2 > b._2){
            (a._1, a._2, -3)
          }else{
            (b._1, b._2, -3)
          }
        }else if(a._3 == -1 && b._3 == -1){
            a
        }else{
          if(a._2 > b._2){
            (a._1, a._2, b._2)
          }else{
            (b._1, b._2, a._2)
          }
        }
    }//mergeMsg end

    val resultGraph = graph.pregel((-1.asInstanceOf[VertexId],0.0,0.0), 4100)(vprog, sendmsg, mergeMsg)
    println(resultGraph.vertices.collect.mkString("\n"))
    println(resultGraph.vertices.filter(a => a._2.isInstanceOf[PersonVD]).map(a => (a._1, a._2.asInstanceOf[PersonVD].assignedObj)).collect().mkString("\n"))
  }
}
