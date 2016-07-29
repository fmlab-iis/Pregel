package org.apache.spark.graphx.lib

import org.apache.spark.SparkContext
import org.apache.spark.graphx.{EdgeTriplet, _}
import org.apache.spark.rdd.RDD
import org.apache.log4j.Logger
import org.apache.log4j.Level

object BMatching {

  def main(args: Array[String]) {
    if (args.length == 0) {
      System.err.println("Usage: BMatching <host> [<slices>]")
      System.exit(1)
    }
    Logger.getLogger("org").setLevel(Level.OFF)
    Logger.getLogger("akka").setLevel(Level.OFF)

    val sc = new SparkContext(args(0), "BMatching")


    // Create an RDD for the vertices
    val vertices: RDD[(VertexId, Int)] =
      sc.parallelize(Array((1L, 3), (2L, 2),
        (3L, 2), (4L, 1), (5L, 1)))

    // Create an RDD for edges
    val relationships: RDD[Edge[Int]] =
      sc.parallelize(Array(Edge(1L, 5L, 3), Edge(1L, 4L, 2),
        Edge(2L, 5L, 5), Edge(1L, 3L, 1),
        Edge(2L, 3L, 6), Edge(3L, 4L, 100)))

    // Create the graph
    val graph = Graph(vertices, relationships)

    println("-----------------------------------------------------")

    def initialize(g: Graph[Int, Int],
                   maxIterations: Int): Graph[(Int, Set[Edge[Int]], Set[Edge[Int]]), Int] = {

      val tmpGraph = g.mapVertices((vid: VertexId, attr: Int) => (attr, Set[Edge[Int]](), Set[Edge[Int]]()))

      val initialMsg = (Set[Edge[(Int)]](), 0)

      def vprog(vertexId: VertexId, value: (Int, Set[Edge[Int]], Set[Edge[Int]]), message: (Set[Edge[Int]], Int)): (Int, Set[Edge[Int]], Set[Edge[Int]]) = {
        if (message._1 == null) {
          (value._1, value._2, value._3)
        }
        else {
          (value._1, message._1.toSeq.sortWith(_.attr > _.attr).take(value._1).toSet, value._3)
        }
      }

      def sendMsg(triplet: EdgeTriplet[(Int, Set[Edge[Int]], Set[Edge[Int]]), Int]): Iterator[(VertexId, (Set[Edge[Int]], Int))] = {
        val a = Edge(srcId = triplet.srcId, dstId = triplet.dstId, attr = triplet.attr)
        val tmp: Set[Edge[Int]] = Set(a)
        Iterator((triplet.dstId, (tmp, triplet.dstAttr._1)), (triplet.srcId, (tmp, triplet.srcAttr._1)))
      }

      def mergeMsg(msg1: (Set[Edge[Int]], Int), msg2: (Set[Edge[Int]], Int)): (Set[Edge[Int]], Int) = {
        val sum = msg1._1 ++ msg2._1
        (sum.toSeq.sortWith(_.attr > _.attr).take(msg1._2).toSet, msg1._2)
      }

      tmpGraph.pregel(initialMsg, maxIterations, EdgeDirection.Out)(vprog, sendMsg, mergeMsg)
    }


    val newGraph = initialize(graph, 1)



    // Check the graph
    //graph.vertices.collect.foreach(println)

    def run(graph: Graph[(Int, Set[Edge[Int]], Set[Edge[Int]]), Int],
            maxIterations: Int): Graph[(Int, Set[Edge[Int]], Set[Edge[Int]]), Int] = {

      val initialMsg = Set[Edge[Int]]()

      def vprog(vertexId: VertexId, value: (Int, Set[Edge[Int]], Set[Edge[Int]]), message: Set[Edge[Int]]): (Int, Set[Edge[Int]], Set[Edge[Int]]) = {
        if (value._2 == null || value._1 == 0 || message.intersect(value._2) == null) {
          (value._1, value._2, value._3)
        }
        else {
          val intersection = message.intersect(value._2)
          val newValue_1 = value._1 - intersection.size
          val newValue_2 = value._2 -- intersection
          val newValue_3 = value._3 ++ intersection

          (newValue_1, newValue_2, newValue_3)
        }
      }

      def sendMsg(triplet: EdgeTriplet[(Int, Set[Edge[Int]], Set[Edge[Int]]), Int]): Iterator[(VertexId, Set[Edge[Int]])] = {
        if (triplet.dstAttr._1 == 0 || triplet.srcAttr._1 == 0)
          Iterator.empty
        else {
          val set_s = triplet.srcAttr._2
          val set_d = triplet.dstAttr._2
          Iterator((triplet.dstId, set_s), (triplet.srcId, set_d))
        }
      }

      def mergeMsg(msg1: Set[Edge[Int]], msg2: Set[Edge[Int]]): Set[Edge[Int]] = {
        if (msg1 == null && msg2 == null) null
        else  msg1.union(msg2)
      }

      graph.pregel(initialMsg, maxIterations, EdgeDirection.Out)(vprog, sendMsg, mergeMsg)

    }

    println("---------------------------------------------")

    run(newGraph, 20).vertices.foreach(println)


  }


}
