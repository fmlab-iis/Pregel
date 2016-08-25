package org.apache.spark.graphx.lib

import org.apache.spark.SparkContext
import org.apache.spark.graphx.{EdgeTriplet, _}
import org.apache.spark.rdd.RDD
import org.apache.log4j.Logger
import org.apache.log4j.Level

object TspProblem {

  def main(args: Array[String]) {
    if (args.length == 0) {
      System.err.println("Usage: TspProblem <host> [<slices>]")
      System.exit(1)
    }
    Logger.getLogger("org").setLevel(Level.OFF)
    Logger.getLogger("akka").setLevel(Level.OFF)

    val sc = new SparkContext(args(0), "TspProblem")


    val relationships: RDD[Edge[Int]] =
      sc.textFile("./"+args(1)+"-"+args(2)+"-"+args(3)+"-"+args(4)+"-"+args(5)+"-edge.txt").map { line =>
        val fields = line.split(" ")
        Edge(fields(0).toLong, fields(1).toLong, fields(2).toInt)
      }

    val vertices: RDD[(VertexId, Int)] =
      sc.textFile("./"+args(1)+"-"+args(2)+"-"+args(3)+"-"+args(4)+"-"+args(5)+"-vertex.txt").map { line =>
        val fields = line.split(" ")
        (fields(0).toLong, 0)
      }

    // Create the graph
    val graph = Graph(vertices, relationships)

    //graph.edges.foreach(println)

    type P = (String, Int)
    object P { def apply(i: String, s: Int): P = (i, s) }

    def initialize(g: Graph[Int, Int],
                   maxIterations: Int, numVertices: Int): Graph[(Int,  Set[P],  Set[P]), Int] = {

      val tmpGraph = g.mapVertices((vid: VertexId, attr: Int) => ( numVertices, Set[P](), Set[P]()))

      val initialMsg = (Set[P]())

      def vprog(vertexId: VertexId, value: (Int,  Set[P],  Set[P]), message: (Set[P])): (Int,  Set[P],  Set[P]) = {
        if(vertexId == 1){
          val a = P("1",0)
          val tmp : Set[P] = Set(a)
          (value._1, tmp, Set[P]())
        }else{
          (value._1, Set[P](), Set[P]())
        }
      }

      def sendMsg(triplet: EdgeTriplet[(Int, Set[P], Set[P]), Int]): Iterator[(VertexId, (Set[P]))] = {
        Iterator.empty
      }

      def mergeMsg(msg1: (Set[P]), msg2: (Set[P])): (Set[P]) = {
        Set[P]()
      }

      tmpGraph.pregel(initialMsg, maxIterations, EdgeDirection.Out)(vprog, sendMsg, mergeMsg)
    }

    val ini_graph = initialize(graph, 1, graph.numVertices.toInt)
    

    def run(g: Graph[(Int,  Set[P],  Set[P]), Int],
                   maxIterations: Int): Graph[(Int,  Set[P],  Set[P], Int), Int] = {

      val initialMsg = (Set[P]())

      val tmpGraph = g.mapVertices((vid: VertexId, attr: (Int,  Set[P],  Set[P])) => (attr._1, attr._2, attr._3, 0))


      def vprog(vertexId: VertexId, value: (Int,  Set[P],  Set[P], Int), message: (Set[P])): (Int,  Set[P],  Set[P], Int) = {

        var newvalue_3 = value._3
        var newvalue_2 = message
        for(a <- message) {
          if(a._1.length  == value._1 + 1){
            newvalue_3 += a
            newvalue_3 = Set[P]() + newvalue_3.minBy(_._2)
            newvalue_2 -= a
          }
        }
        if(vertexId == 1 && value._4 == 0){
          //println("Round:"+value._4+" "+vertexId+": "+value._2)
          (value._1, value._2, newvalue_3, 1)
        }else{
          //println("Round:"+value._4+" "+vertexId+": "+newvalue_2)
          (value._1, newvalue_2, newvalue_3, value._4+1)
        }

      }

      def sendMsg(triplet: EdgeTriplet[(Int, Set[P], Set[P], Int), Int]): Iterator[(VertexId, Set[P])] = {
        var tmp_1 : Set[P] = Set[P]()
        if(triplet.dstAttr._2 != Set[P]()) {
          //If not empty
          for (a <- triplet.dstAttr._2) {
            if (a._1.indexOf(triplet.srcId.toString()) == -1) {
              //If not been through yet!
              val tmp_s = a._1 + triplet.srcId.toString
              val tmp_w = a._2 + triplet.attr
              val p = P(tmp_s, tmp_w)
              tmp_1 = tmp_1 + p
            }else if(a._1.length == triplet.dstAttr._1 && triplet.srcId == 1){
              val tmp_s = a._1 + triplet.srcId.toString
              val tmp_w = a._2 + triplet.attr
              val p = P(tmp_s, tmp_w)
              tmp_1 = tmp_1 + p
            }
          }
        }
        var tmp_2 : Set[P] = Set[P]()
        if(triplet.srcAttr._2 != Set[P]()){ //If not empty
            for (a <- triplet.srcAttr._2){
              if(a._1.indexOf(triplet.dstId.toString()) == -1){
                //If not been through yet!
                val tmp_s = a._1+triplet.dstId.toString
                val tmp_w = a._2+triplet.attr
                val p = P(tmp_s,tmp_w)
                tmp_2 = tmp_2 + p
              }else if(a._1.length == triplet.dstAttr._1 && triplet.dstId == 1){
                val tmp_s = a._1 + triplet.dstId.toString
                val tmp_w = a._2 + triplet.attr
                val p = P(tmp_s, tmp_w)
                tmp_2 = tmp_2 + p
              }
            }
        }
        return Iterator((triplet.srcId, tmp_1),(triplet.dstId, tmp_2))
      }

      def mergeMsg(msg1: (Set[P]), msg2: (Set[P])): (Set[P]) = {
        msg1 ++ msg2
      }

      tmpGraph.pregel(initialMsg, maxIterations, EdgeDirection.Out)(vprog, sendMsg, mergeMsg)
    }

    run(ini_graph, ini_graph.numVertices.toInt).vertices.foreach(println)


  }


}
