import org.apache.spark.graphx._
import org.apache.spark.graphx.util.GraphGenerators
import org.apache.spark._
import org.apache.spark.rdd.RDD

import scala.io._
import org.w3c.dom.Attr

import scala.collection.JavaConverters._
object facilityLocation {
  def main(args: Array[String]): Unit = {

    val conf = new SparkConf().setAppName("facilityLocation")
    val sc = new SparkContext(conf)

    val vertex: RDD[(VertexId, (Int, Int, Int))] = sc.parallelize(
        Array((1L, (0, 20, 1)),//unopen,cost,tag
              (2L, (0, 11, 1)),
              (3L, (0, 0, 1)),//unfrozen=0,frozen!=0
              (4L, (0, 0, 1)),
              (5L, (0, 0, 1)),
              (6L, (0, 0, 1))))
    val edge: RDD[Edge[Int]] = sc.parallelize(
        Array(Edge(1, 3, 10),//facility is src
              Edge(1, 4, 3),
              Edge(1, 5, 2),
              Edge(1, 6, 3),
              Edge(2, 3, 10),
              Edge(2, 4, 4),
              Edge(2, 5, 7),
              Edge(2, 6, 5)))
    //val V: RDD[Verte1xId,(String,String)]=sc.parallelize(Array((1L,("ddf","jio")),(2L,("ddf","jio")),(3L,("ddf","jio")),(4L,("ddf","jio")),(5L,("ddf","jio")),(6L,("ddf","jio"))))
    val graph = Graph(vertex, edge)
   // val accum = sc.longAccumulator("My Accumulator")
    var radius =sc.accumulator(1)
    val ep = 1

    def vertexProgram(id: VertexId,
                      attr: (Int, Int, Int),
                      msg: Int): (Int, Int, Int) = {
      if (attr._3 == 1) { //the first phase , just expanding radius . radius is globle variable
        //we need this phase since we just have to expanding radius in this phase
        radius += ep
        return (attr._1, attr._2, 2) //the third is the tag of phases
      } else if (attr._3 == 2) {
        //Message is sigma (radius - dist)
        //open the facility
        if (msg <= attr._2 && attr._1 == 0 && attr._2 != 0) { //attr._2 != 0 make sure the node is not client
                                                              //attr._2 of facility is cost, attr._1==zero means unopen
                                                              //cuz the attr._2 of client is always zero
          return (1, attr._2, 3) // opening the facility , the first parameter indicate if the facility is openned
        } else {
          return (attr._1, attr._2, 3) //If there is no facility that needed to be open, modify phase parameter
        }
      } else { //phase 3
        //frozen the client
        //the message is a bool indicate whether client is frozened
        if (attr._2 == 0 && attr._1==0 && msg != 0) { // the attr._2 of client is always zero
                                                      //attr._1==0 means the client is unfrozen //msg!=0 frozen
          return (radius.localValue, attr._2, 1) // record the current dist in first parameter
        } else {
          return (attr._1, attr._2, 1)//do nothing
        }
      }
    }

    def sendMessage(
        edge: EdgeTriplet[(Int, Int, Int), Int]): Iterator[(VertexId, Int)] = {
      if (edge.srcAttr._3 == 1) {
        //msg is nothing
        Iterator((edge.srcId, 0))
      } else if (edge.srcAttr._3 == 2) {//phase2
        //message is radius - dist
        if(edge.srcAttr._1 == 0){ //if unopen
        val the_msg =
          if ((radius.localValue - edge.attr) > 0) radius.localValue - edge.attr else 0
            Iterator((edge.srcId, the_msg))
        }
        else Iterator.empty //if facility is open, 送一個意意的訊息 防止邊死掉
      } else { // third phase
        //message is a bool
        if (edge.srcAttr._1 == 1 && edge.attr < radius.localValue) { //if facility is open, frozen the client, else Iterator itself
          Iterator((edge.dstId, 1))//msg is a tag to identify frozened
        } else {
          Iterator.empty
        }
      }
    }

    def mergeMssage(a: Int, b: Int): Int = {
      a + b
    }

    val facility_location =
      Pregel(graph, 0)(vertexProgram, sendMessage, mergeMssage)
  }
}

