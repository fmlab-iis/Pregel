import org.apache.spark.graphx._
import org.apache.spark.graphx.util.GraphGenerators
import org.apache.spark._
import org.apache.spark.rdd.RDD

import scala.collection.JavaConverters._
object Kcore {
  def main(args: Array[String]): Unit = {

    val path: String = args(0)
    val coreNumber0: String = args(1)
    val coreNumber = coreNumber0.toInt
    val conf = new SparkConf().setMaster("local[4]").setAppName("K-core")
    val sc = new SparkContext(conf)
    val graph1 = GraphLoader.edgeListFile(sc, path)
    val degree = graph1.degrees //It is the attribute of vertex
    val edges = graph1.edges

    val initgraph0 = Graph[Int, Int](degree, edges)


    def vertexProgram(id: VertexId, attr: Int, msgDegree: Int): Int = {
      val degree = attr - msgDegree
      if (degree > 0 && degree < coreNumber) 0
      else if (degree == 0 && degree <= -1) -1
      else degree
    }

    def sendMessage(edge: EdgeTriplet[Int, Int]): Iterator[(VertexId, Int)] = {
      if (edge.dstAttr > 0 && edge.srcAttr == 0) {
        Iterator((edge.dstId, 1), (edge.srcId, 1))
      } else if (edge.srcAttr > 0 && edge.dstAttr == 0) {
        Iterator((edge.srcId, 1), (edge.dstId, 1))
      } else {
        Iterator()
      }
    }

    def messageCombiner(a: Int, b: Int): Int = { a + b }

    val kcoreGraph = Pregel(initgraph0, initialMsg = 0)(vertexProgram,
                                                        sendMessage,
                                                        messageCombiner)
    def answer = kcoreGraph.subgraph((a) => a.srcAttr > 0 && a.dstAttr > 0)
    println(answer.edges)
  }
}
