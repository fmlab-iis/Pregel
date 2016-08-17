package org.apache.spark.graphx.lib

import org.apache.spark.SparkContext
import org.apache.spark.graphx.{EdgeTriplet, _}
import org.apache.spark.rdd.RDD
import org.apache.log4j.Logger
import org.apache.log4j.Level
import java.io._


object GraphTest {

  def main(args: Array[String]) {
    if (args.length == 0) {
      System.err.println("Usage: GraphTest <host> [<slices>]")
      System.exit(1)
    }
    Logger.getLogger("org").setLevel(Level.OFF)
    Logger.getLogger("akka").setLevel(Level.OFF)



    val sc = new SparkContext(args(0), "GraphTest")

    val relationships: RDD[Edge[Int]] =
      sc.textFile("./"+args(1)+"-"+args(2)+"-"+args(3)+"-"+args(4)+"-"+args(5)+"-edge.txt").map { line =>
        val fields = line.split(" ")
        Edge(fields(0).toLong, fields(1).toLong, fields(2).toInt)
      }

    val vertices: RDD[(VertexId, Int)] =
      sc.textFile("./"+args(1)+"-"+args(2)+"-"+args(3)+"-"+args(4)+"-"+args(5)+"-vertex.txt").map { line =>
        val fields = line.split(" ")
        (fields(0).toLong, fields(1).toInt)
      }

    // Create the graph
    val graph = Graph(vertices, relationships)


    def initialize(g: Graph[Int, Int],
                   maxIterations: Int): Graph[(Int, Set[Edge[Int]], Set[Edge[Int]], Set[Edge[Int]]), Int] = {

      val tmpGraph = g.mapVertices((vid: VertexId, attr: Int) => (attr, Set[Edge[Int]](), Set[Edge[Int]](), Set[Edge[Int]]()))

      val initialMsg = (Set[Edge[(Int)]](), 0)

      def vprog(vertexId: VertexId, value: (Int, Set[Edge[Int]], Set[Edge[Int]], Set[Edge[Int]]), message: (Set[Edge[Int]], Int)): (Int, Set[Edge[Int]], Set[Edge[Int]], Set[Edge[Int]]) = {
        if (message._1 == null) {
          (value._1, value._2, value._3, value._4)
        }
        else {
          (value._1, message._1.toSeq.sortWith(_.attr > _.attr).toSet, value._3, value._4)
        }
      }

      def sendMsg(triplet: EdgeTriplet[(Int, Set[Edge[Int]], Set[Edge[Int]], Set[Edge[Int]]), Int]): Iterator[(VertexId, (Set[Edge[Int]], Int))] = {
        val a = Edge(srcId = triplet.srcId, dstId = triplet.dstId, attr = triplet.attr)
        val tmp: Set[Edge[Int]] = Set(a)
        Iterator((triplet.dstId, (tmp, triplet.dstAttr._1)), (triplet.srcId, (tmp, triplet.srcAttr._1)))
      }

      def mergeMsg(msg1: (Set[Edge[Int]], Int), msg2: (Set[Edge[Int]], Int)): (Set[Edge[Int]], Int) = {
        (msg1._1 ++ msg2._1, msg1._2)
      }

      tmpGraph.pregel(initialMsg, maxIterations, EdgeDirection.Out)(vprog, sendMsg, mergeMsg)

    }


    val newGraph = initialize(graph, 1)


    //newGraph.vertices.foreach(println)





    // Check the graph
    //graph.vertices.collect.foreach(println)

    def run(graph: Graph[(Int, Set[Edge[Int]], Set[Edge[Int]], Set[Edge[Int]]), Int],
            maxIterations: Int): Graph[(Int, Set[Edge[Int]], Set[Edge[Int]], Set[Edge[Int]]), Int] = {

      val initialMsg = Set((Set[Edge[Int]](), 0))
      //Empty Set.

      def vprog(vertexId: VertexId, value: (Int, Set[Edge[Int]], Set[Edge[Int]], Set[Edge[Int]]), message: Set[(Set[Edge[Int]], Int)]): (Int, Set[Edge[Int]], Set[Edge[Int]], Set[Edge[Int]]) = {
        var newValue_1 = value._1
        var newValue_2 = value._2
        var newValue_3 = value._3
        var newValue_4 = value._4
        var neededCandidateNum = 0

        for (op <- message) op._2 match{
          case 0 => {
            neededCandidateNum = value._1 - value._3.size
            newValue_3 = value._3 ++ value._2.toSeq.sortWith(_.attr > _.attr).take(neededCandidateNum).toSet
            newValue_2 = value._2 -- newValue_3
            newValue_4 = value._4
            newValue_1 = value._1
            //println("OP: 0, ID: "+vertexId+", TARGET: "+op._1+", CAPACITY: "+newValue_1)

          }
          case 1 => {
            //println("ID => "+vertexId+" received "+op._1)
            newValue_1 = newValue_1 - 1
            newValue_3 = newValue_3 -- op._1
            newValue_4 = newValue_4 ++ op._1

            //println("OP: 1, ID: "+vertexId+", TARGET: "+op._1+", CAPACITY: "+newValue_1)

          }
          case 2 => {
            newValue_2 = newValue_2 -- op._1
            newValue_3 = newValue_3 -- op._1

            neededCandidateNum = value._1 - value._3.size
            if(neededCandidateNum > 0){
              newValue_3 = newValue_3 ++ value._2.toSeq.sortWith(_.attr > _.attr).take(neededCandidateNum).toSet
              newValue_2 = newValue_2 -- newValue_3
            }
            //println("OP: 2, ID: "+vertexId+", TARGET: "+op._1)


          }
          case 3 => {
            neededCandidateNum = value._1 - value._3.size
            if(neededCandidateNum > 0){
              newValue_3 = value._3 ++ value._2.toSeq.sortWith(_.attr > _.attr).take(neededCandidateNum).toSet
              newValue_2 = value._2 -- newValue_3
              newValue_4 = value._4
            }
            //println("OP: 3, ID: "+vertexId+", TARGET: "+op._1)
          }
          case _ => {
            println("Match Error")
          }

        }

        (newValue_1, newValue_2, newValue_3, newValue_4)

      }

      def sendMsg(triplet: EdgeTriplet[(Int, Set[Edge[Int]], Set[Edge[Int]], Set[Edge[Int]]), Int]): Iterator[(VertexId, Set[(Set[Edge[Int]], Int)])] = {
        val self = Edge(srcId = triplet.srcId, dstId = triplet.dstId, attr = triplet.attr)

        if(triplet.srcAttr._2(self) || triplet.srcAttr._3(self) || triplet.dstAttr._2(self) || triplet.dstAttr._3(self)){
            if(triplet.srcAttr._1 == 0 || triplet.dstAttr._1 == 0){
              val tmp: Set[(Set[Edge[Int]], Int)] = Set((Set(self),2))
              return Iterator((triplet.dstId, tmp), (triplet.srcId, tmp))
            }
            if(triplet.srcAttr._3(self) && triplet.dstAttr._3(self)){
              val tmp: Set[(Set[Edge[Int]], Int)] = Set((Set(self),1))
              return Iterator((triplet.dstId, tmp), (triplet.srcId, tmp))
            }
        }else{
          val tmp: Set[(Set[Edge[Int]], Int)] = Set((Set(self),3))
          return Iterator((triplet.dstId, tmp), (triplet.srcId, tmp))
        }
        val tmp: Set[(Set[Edge[Int]], Int)] = Set((Set(self),3))
        return Iterator((triplet.dstId, tmp), (triplet.srcId, tmp))
      }

      def mergeMsg(msg1: Set[(Set[Edge[Int]], Int)], msg2 : Set[(Set[Edge[Int]], Int)]): Set[(Set[Edge[Int]], Int)] = {
        if (msg1 == null && msg2 == null) null
        else  msg1.union(msg2)
      }

      graph.pregel(initialMsg, maxIterations, EdgeDirection.Out)(vprog, sendMsg, mergeMsg)

    }



    var fk = Set[Edge[Int]]()

    val result = run(newGraph, newGraph.numEdges.toInt)

    println("--------------")
    //result.vertices.foreach(x => println(x._1+" "+x._2._1))
    result.vertices.foreach(x => println(x._1+" "+x._2._1+" "+x._2._2+" "+x._2._3))
    //println("--------------")
    //result.vertices.foreach(x => println(x._1+" "+x._2._4))

        val whereami = System.getProperty("user.dir")
        println(whereami)


        result.vertices.foreach(_._2._4.foreach({x => val tmp: Set[Edge[Int]] = Set(x)
          var sum=0
          fk = fk.union(tmp)
          fk.foreach({y => sum += y.attr})
          val sw = new PrintWriter(new File("./"+args(1)+"-"+args(2)+"-"+args(3)+"-"+args(4)+"-"+args(5)+"-poutput.txt"))
          sw.close()
          fk.foreach({ y =>
            val fw = new FileWriter("./"+args(1)+"-"+args(2)+"-"+args(3)+"-"+args(4)+"-"+args(5)+"-poutput.txt", true)
            fw.append(y.toString+ "\n")
            fw.close() })

          val writer = new PrintWriter(new File("./"+args(1)+"-"+args(2)+"-"+args(3)+"-"+args(4)+"-"+args(5)+"-presult.txt"))
          writer.write(sum.toString + "\n")
          //println(sum)
          writer.close()}))




  }



}
