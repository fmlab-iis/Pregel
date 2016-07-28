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
    val vertices: RDD[(VertexId, (Int, Set[Edge[Int]], Set[Edge[Int]]))] =
      sc.parallelize(Array((1L, (3, Set(Edge(1L, 5L, 3),Edge(1L, 4L, 2),Edge(1L, 3L, 1)), Set[Edge[Int]]())),
        (2L, (2, Set(Edge(2L, 5L, 5),Edge(2L, 3L, 6)), Set[Edge[Int]]())),
        (3L, (2, Set(Edge(2L, 3L, 6),Edge(3L, 4L, 100)), Set[Edge[Int]]())),
        (4L, (1, Set(Edge(3L, 4L, 100)), Set[Edge[Int]]())),
        (5L, (1, Set(Edge(2L, 5L, 5)), Set[Edge[Int]]()))))

    // Create an RDD for edges
    val relationships: RDD[Edge[Int]] =
      sc.parallelize(Array(Edge(1L, 5L, 3), Edge(1L, 4L, 2),
        Edge(2L, 5L, 5), Edge(1L, 3L, 1),
        Edge(2L, 3L, 6), Edge(3L, 4L, 100)))

    // Create the graph
    val graph = Graph(vertices, relationships)

    // Check the graph
    graph.vertices.foreach(println)


    //val graph2 = graph.mapVertices((vid:VertexId, attr:(Int)) => (attr,getTargetEdges(attr),Set[Edge[Int]]()))


    def run(graph: Graph[(Int, Set[Edge[Int]], Set[Edge[Int]]), Int],
                                        maxIterations: Int): Graph[(Int, Set[Edge[Int]], Set[Edge[Int]]), Int] = {

      val initialMsg = Set[Edge[Int]] ()

      def vprog(vertexId: VertexId, value: (Int, Set[Edge[Int]], Set[Edge[Int]]), message: Set[Edge[Int]]): (Int, Set[Edge[Int]], Set[Edge[Int]]) = {
        if (value._2 == null || value._1 == 0 || message.intersect (value._2) == null) {
          return (value._1, value._2, value._3)
        }
        else {
          val intersection = message.intersect (value._2)
          val newValue_1 = value._1 - intersection.size
          val newValue_2 = value._2 -- intersection
          val newValue_3 = value._3 ++ intersection
          return (newValue_1, newValue_2, newValue_3)
        }
    }

      def sendMsg(triplet: EdgeTriplet[(Int, Set[Edge[Int]], Set[Edge[Int]]), Int]): Iterator[(VertexId, Set[Edge[Int]])] = {
        if (triplet.dstAttr._1 == 0 || triplet.srcAttr._1 == 0)
          Iterator.empty
        else {
          val set_s = triplet.srcAttr._2
          val set_d = triplet.dstAttr._2
          Iterator ((triplet.dstId, set_s), (triplet.srcId, set_d) )
        }
      }

      def mergeMsg(msg1: Set[Edge[Int]], msg2: Set[Edge[Int]]): Set[Edge[Int]] = {
        if (msg1 == null && msg2 == null) return null
        else return msg1.union (msg2)
    }
      val minGraph = graph.pregel (initialMsg, maxIterations, EdgeDirection.Out) (vprog, sendMsg, mergeMsg)

      return minGraph

    }

    println("---------------------------------------------")

    run(graph,20).vertices.foreach(println)


  }




}
