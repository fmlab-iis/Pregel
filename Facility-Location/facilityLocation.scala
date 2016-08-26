import org.apache.spark.graphx._
import org.apache.spark.graphx.util.GraphGenerators
import org.apache.spark._
import org.apache.spark.rdd.RDD

import scala.io._
import org.w3c.dom.Attr

import scala.collection.JavaConverters._
object facilityLocation {
  def main(args: Array[String]): Unit = {

    val conf =
      new SparkConf().setAppName("facilityLocation").setMaster("local[4]")
    val sc = new SparkContext(conf)

    val vertex: RDD[(VertexId, (Int, Int, Int,Int))] = sc.parallelize(
        Array((1L, (0, 4, 1,0)), //unopen,cost,radius,tag
              (2L, (0, 110, 1,0)),
              (3L, (0, 0, 1,0)), //unfrozen=0,frozen!=0,first parameter
              (4L, (0, 0, 1,0)),
              (5L, (0, 0, 1,0)),
              (6L, (0, 0, 1,0))))
    val edge: RDD[Edge[Int]] = sc.parallelize(
        Array(Edge(1, 3, 5), //facility is src,client is destination
              Edge(1, 4, 5),
              Edge(1, 5, 5),
              Edge(1, 6, 5),
              Edge(2, 3, 7),
              Edge(2, 4, 7),
              Edge(2, 5, 10),
              Edge(2, 6, 10)))
    val graph = Graph(vertex, edge)
    val ep = 1
    val init=graph.mapVertices((a,b)=>(b._1,b._2,b._3,1))
    def vertexProgram(id: VertexId,
                      attr: (Int, Int, Int,Int),
                      msg: Int): (Int, Int, Int,Int) = {
      if (attr._3 == 1) { //the first phase , just expanding radius . radius is globle variable
        //we need this phase since we just have to expanding radius in this phase
        return (attr._1, attr._2, 2,attr._4+ep) //the third is the tag of phases
      } else if (attr._3 == 2) { //stage 2
        //Message is sigma (radius - dist)
        //open the facility
        if (msg >= attr._2 && attr._1 == 0 && attr._2 != 0) { //attr._2 != 0 make sure the node is not client
          //attr._2 of facility is cost, attr._1==zero means unopen
          //cuz the attr._2 of client is always zero
          return (1, attr._2, 3,attr._4) // opening the facility , the first parameter indicate if the facility is openned
        } else {
          return (attr._1, attr._2, 3,attr._4) //If there is no facility that needed to be open, modify phase parameter
        }
      } else { //phase 3
        //frozen the client
        //the message is a bool indicate whether client is frozened

        if (attr._2 == 0 && attr._1 == 0 && msg != 0) { // the attr._2 of client is always zero
          //attr._1==0 means the client is unfrozen //msg!=0 frozen
          return (attr._4, attr._2, 1,attr._4) // record the current dist in first parameter
        } else {
          return (attr._1, attr._2, 1,attr._4) //do nothing
        }
      }
    }

    def sendMessage(
        edge: EdgeTriplet[(Int, Int, Int,Int), Int]): Iterator[(VertexId, Int)] = {
      if (edge.srcAttr._3 == 1) {
        //msg is nothing
        Iterator((edge.srcId, 0), (edge.dstId, 0))
      } else if (edge.srcAttr._3 == 2) { //phase2
        //message is radius - dist
        if (edge.srcAttr._1 == 0) { //if unopen
          val the_msg =
            if ((edge.dstAttr._4 - edge.attr) > 0)
              edge.dstAttr._4- edge.attr
            else 0
          
          Iterator((edge.srcId, the_msg), (edge.dstId, 0)) //why???
        } else Iterator.empty //if facility is open,
      } else { // third phase
        //message is a bool
        if (edge.srcAttr._1 == 1 && edge.attr < edge.srcAttr._4) { //if facility is open, frozen the client, else Iterator itself
         println("OOOOO")
          println("dstId: "+edge.dstId)
          println("srcID: "+edge.srcId)
          println("OOOOOO")
          Iterator((edge.dstId, 1), (edge.srcId, 0)) //msg is a tag to identify frozened
        }
        else if(edge.srcAttr._1==0&&edge.dstAttr._1==0){//if the facility is unopen and the client is unfrozen keep the edges alive
          Iterator((edge.srcId,0),(edge.dstId,0))
        }
        else {
          Iterator.empty
        }
      }
    }

    def mergeMssage(a: Int, b: Int): Int = {
      a + b
    }
    val facility_location =
      Pregel(init, 0)(vertexProgram, sendMessage, mergeMssage)
    facility_location.vertices.foreach(println)
  }
}

