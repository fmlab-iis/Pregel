/**
 * This script tries to model and prove correctness of
 * https://github.com/apache/spark/blob/master/graphx/src/main/scala/org/apache/spark/graphx/lib/ConnectedComponents.scala
 */

include "nondet-permutation.dfy"

type VertexId = int
type VertexAttr = array<Distance>
type EdgeAttr = real
type Message = array<Distance>
type Distance = int

class PregelBellmanFordAlgorithm
{
	var numVertices: nat;
	var Infinity : nat;
	var initMsg: Message;
	var graph: array2<EdgeAttr>;
	var sent: array2<bool>;
	var vAttr: array<VertexAttr>;
	var NoEdge: EdgeAttr

	/**
	 * The SendMessage, MergeMessage and VertexProgram functions of the framework.
	 * These three ingredients should suffice to characterize a Pregel algorithm.
	 */

	method SendMessage(src: VertexId, dst: VertexId, w: EdgeAttr) returns (msg: seq<(VertexId, Message)>)
		requires isVertex(src) && isVertex(dst) && isArray(vAttr)
		requires GraphInvariant()
		requires consistent()
		requires adjacent(src, dst)
		modifies sent
		ensures consistent()
		ensures forall m | m in msg :: isVertex(m.0) && isMessageFor(m.1, m.0)
		ensures sent[dst,src] <==> exists j | 0 <= j < numVertices :: vAttr[src][j] > vAttr[dst][j] + 1
	{
		sent[src,dst] := false;
		sent[dst,src] := false;
		msg := [];
		var msg' := new Distance[numVertices];
		var i := 0;
		while i < numVertices
			invariant i <= numVertices
			invariant sent[dst,src] <==> (exists j | 0 <= j < i :: vAttr[src][j] > vAttr[dst][j] + 1)
		{
			if vAttr[src][i] > vAttr[dst][i] + 1
			{
				var j := 0;
				while j < numVertices
					invariant j <= numVertices
					invariant forall k | 0 <= k < j :: msg'[k] == vAttr[dst][k] + 1;
				{
					msg'[j] := vAttr[dst][j] + 1;
					j := j + 1;
				}
				sent[dst,src] := true;
				assert vAttr[src][i] > vAttr[dst][i] + 1; // needed by invariant
				assert forall k | 0 <= k < numVertices :: msg'[k] == vAttr[dst][k] + 1;
				msg := [(src, msg')];
				break;
			}
			i := i + 1;
		}
	}

	method MergeMessage(msg: Message, msg': Message) returns (res: Message)
		requires isArray(msg) && isArray(msg')
		ensures fresh(res) && isArray(res)
		ensures forall i | 0 <= i < numVertices :: res[i] == min(msg[i], msg'[i])
	{
		res := new Distance[numVertices];
		forall i | 0 <= i < numVertices {
			res[i] := min(msg[i], msg'[i]);
		}
	}

	function method min(a: VertexId, b: VertexId): VertexId
	{
		if a >= b then b else a
	}

	method VertexProgram(vid: VertexId, attr: VertexAttr, msg: Message) returns (attr': VertexAttr)
		requires isVertex(vid) && isArray(vAttr) && GraphInvariant0()
		requires msg != initMsg ==> isVertexAttr(vid, attr)
		requires msg != initMsg ==> isMessageFor(msg, vid)
		ensures GraphInvariant0()
		ensures isVertexAttr(vid, attr') && isConsistentAt(vid, attr')
	{
		attr' := new Distance[numVertices];
		if msg == initMsg {
			var dst := 0;
			while dst < numVertices
				invariant dst <= numVertices

				invariant forall j | 0 <= j < dst :: attr'[j] == if vid == j then 0 else Infinity
			{
				attr'[dst] := if vid == dst then 0 else Infinity;
				dst := dst + 1;
			}
		} else {
			var i := 0;
			while i < numVertices
				invariant i <= numVertices
				invariant forall i | 0 <= i < numVertices :: attr[i] <= numVertices ==> connected'(vid, i, attr[i])
				invariant forall i | 0 <= i < numVertices :: msg[i] <= numVertices ==> connected'(vid, i, msg[i])
				invariant forall j | 0 <= j < i :: attr'[j] == min(attr[j], msg[j])
			{
				attr'[i] := min(attr[i], msg[i]);
				i := i + 1;
			}
		}
	}

	/***************************************
	 * User-supplied correctness definitions
	 ***************************************/

	predicate DistancesComputed()
		requires isArray(vAttr) && GraphInvariant0()
		reads this`graph, this`vAttr, this`sent, this`numVertices, this`NoEdge, this`Infinity, vAttr, vAttr[..]
	{
		DistancesComputed'(numVertices)
	}

	predicate DistancesComputed'(dist: nat)
		requires isArray(vAttr) && GraphInvariant0()
		requires 0 <= dist < Infinity
		reads this`graph, this`vAttr, this`sent, this`numVertices, this`NoEdge, this`Infinity, vAttr, vAttr[..]
	{
		forall i,j | 0 <= i < numVertices && 0 <= j < numVertices ::
			(connected'(i, j, dist) ==> 0 <= vAttr[i][j] <= dist)
			&&
			(vAttr[i][j] < Infinity ==> connected'(i, j, vAttr[i][j]))
	}

	/*************************************************
	 * User-supplied correctness predicates and lemmas
	 *************************************************/

	method Validate()
		requires numVertices > 1
		requires isArray(vAttr) && GraphInvariant0()
		modifies this`numVertices, vAttr, sent
	{
		var maxNumIterations :| maxNumIterations > 0;
		var numIterations := Pregel(maxNumIterations);

		if numIterations < maxNumIterations {
			assert !active() && noCollisions();
			CollisionLemma();
			assert noCollisionsInductive(numVertices, numVertices);
			DistanceLemma();
			assert DistancesComputed();
		}
		assert numIterations < maxNumIterations ==> DistancesComputed();
	}

	predicate noCollisions()
		requires isArray(vAttr) && GraphInvariant0()
		reads this`graph, this`vAttr, this`sent, this`numVertices, this`NoEdge, this`Infinity, vAttr, vAttr[..]
	{
		forall vid | 0 <= vid < numVertices :: noCollisionsAt(vid)
	}

	predicate noCollisionsAt(src: VertexId)
		requires isVertex(src) requires isArray(vAttr) && GraphInvariant0()
		reads this`graph, this`vAttr, this`sent, this`numVertices, this`NoEdge, this`Infinity, vAttr, vAttr[..]
	{
		forall dst | 0 <= dst < numVertices :: noCollisionBetween(src, dst)
	}

	predicate noCollisionBetween(src: VertexId, dst: VertexId)
		requires isVertex(src) && isVertex(dst) && isArray(vAttr) && GraphInvariant0()
		reads this`graph, this`vAttr, this`sent, this`numVertices, this`NoEdge, this`Infinity, vAttr, vAttr[..]
	{
		(src == dst ==> vAttr[src][dst] == 0)
		&&
		(adjacent(src, dst) && !sent[src,dst] && !sent[dst,src] ==>
			forall i | 0 <= i < numVertices :: vAttr[src][i] <= vAttr[dst][i] + 1)
	}

	predicate consistent()
		requires isArray(vAttr) && GraphInvariant0()
		reads this`graph, this`vAttr, this`sent, this`numVertices, this`NoEdge, this`Infinity, vAttr, vAttr[..]
	{
		(forall i | 0 <= i < numVertices :: vAttr[i][i] == 0)
		&&
		(forall src,dst | 0 <= src < numVertices && 0 <= dst < numVertices ::
			vAttr[src][dst] <= numVertices ==> connected'(src, dst, vAttr[src][dst]))
	}

	predicate isConsistentAt(vid: VertexId, dist: array<Distance>)
		requires  isMatrix(graph) && isVertex(vid) && isArray(dist)
		reads this`graph, this`NoEdge, this`numVertices, dist
	{
		forall dst | 0 <= dst < numVertices ::
			dist[dst] <= numVertices ==> connected'(vid, dst, dist[dst])
	}

	predicate noCollisionsInductive(srcBound: VertexId, dstBound: VertexId)
		requires srcBound <= numVertices && dstBound <= numVertices
		requires isArray(vAttr) && GraphInvariant0()
		reads this`graph, this`vAttr, this`sent, this`numVertices, this`NoEdge, this`Infinity, vAttr, vAttr[..]
	{
		forall src,dst | 0 <= src < srcBound && 0 <= dst < dstBound ::
			(src == dst ==> vAttr[src][dst] == 0)
			&&
			(adjacent(src, dst) && !sent[src,dst] && !sent[dst,src] ==>
				forall i | 0 <= i < numVertices :: vAttr[src][i] <= vAttr[dst][i] + 1)
	}

	lemma CollisionLemma()
		requires isArray(vAttr) && GraphInvariant0()
		ensures noCollisions() ==> noCollisionsInductive(numVertices, numVertices)
	{
		if noCollisions()
		{
			var src := 0;
			while src < numVertices
				invariant src <= numVertices
				invariant noCollisionsInductive(src, numVertices)
			{
				var dst := 0;
				assert noCollisionsAt(src);
				while dst < numVertices
					invariant dst <= numVertices
					invariant noCollisionsInductive(src, dst)
					invariant forall vid | 0 <= vid < dst ::
						(src == vid ==> vAttr[src][vid] == 0) &&
						(adjacent(src, vid) && !sent[src,vid] && !sent[vid,src] ==>
							forall i | 0 <= i < numVertices :: vAttr[src][i] <= vAttr[vid][i] + 1)
				{
					assert noCollisionBetween(src, dst);
					assert adjacent(src, dst) && !sent[src,dst] && !sent[dst,src] ==>
						(src == dst ==> vAttr[src][dst] == 0) &&
						(forall i | 0 <= i < numVertices :: vAttr[src][i] <= vAttr[dst][i] + 1);
					dst := dst + 1;
				}
				src := src + 1;
			}
		}
	}

	lemma DistanceLemma()
		requires isArray(vAttr)
		requires GraphInvariant0()
		requires vAttrInvariant()
		requires consistent()
		ensures !active() && noCollisionsInductive(numVertices, numVertices) ==> DistancesComputed()
	{
		if !active() && noCollisionsInductive(numVertices, numVertices)
		{
			DistanceLemma'(numVertices);
		}
	}

	lemma DistanceLemma'(dist: nat)
		requires isArray(vAttr)
		requires GraphInvariant0()
		requires vAttrInvariant()
		requires 0 <= dist < Infinity
		requires consistent()
		requires !active() && noCollisionsInductive(numVertices, numVertices)
		ensures DistancesComputed'(dist)
	{
		if dist > 0
		{
			DistanceLemma'(dist - 1);

			var src := 0;
			while src < numVertices
				invariant src <= numVertices
				invariant forall i,j | 0 <= i < src && 0 <= j < numVertices :: connected'(i, j, dist) ==> vAttr[i][j] <= dist
			{
				var dst := 0;
				while dst < numVertices
					invariant dst <= numVertices
					invariant forall j | 0 <= j < dst :: connected'(src, j, dist) ==> vAttr[src][j] <= dist
				{
					dst := dst + 1;
				}
				src := src + 1;
			}
		}
	}

	/******************
	 * Helper preicates
	 ******************/

	/* Use this with caution. See https://dafny.codeplex.com/workitem/146. */
	function method active(): bool
		requires isMatrix(sent)
		reads this`sent, this`numVertices
	{
		exists i,j | 0 <= i < numVertices && 0 <= j < numVertices :: sent[i,j]
	}

	function method adjacent(src: VertexId, dst: VertexId): bool
		requires isMatrix(graph) && isVertex(src) && isVertex(dst)
		reads this`graph, this`NoEdge, this`numVertices
	{
		graph[src,dst] != NoEdge
	}

	/* Check if dst is reachable from src. */
	predicate connected(src: VertexId, dst: VertexId)
		requires isMatrix(graph) && isVertex(src) && isVertex(dst)
		reads this`graph, this`NoEdge, this`numVertices
	{
		exists d :: 0 <= d <= numVertices && connected'(src, dst, d)
	}

	predicate connected'(src: VertexId, dst: VertexId, dist: int)
		requires isMatrix(graph) && isVertex(src) && isVertex(dst)
		reads this`graph, this`NoEdge, this`numVertices
		decreases dist
	{
		if dist < 0 then
			false
		else
		if dist == 0 then
			src == dst
		else
		if dist == 1 then
			adjacent(src, dst)
		else
			exists next | 0 <= next < numVertices ::
				adjacent(src, next) && connected'(next, dst, dist - 1)
	}

	predicate isVertex(vid: int)
		reads this`numVertices
	{
		0 <= vid < numVertices
	}

	predicate isArray<T> (arr: array<T>)
		reads this`numVertices
	{
		arr != null && arr.Length == numVertices
	}

	predicate isMatrix<T> (mat: array2<T>)
		reads this`numVertices
	{
		mat != null && mat.Length0 == numVertices && mat.Length1 == numVertices
	}

	predicate isMessageFor(msg: array<Distance>, vid: VertexId)
		requires isVertex(vid) && isMatrix(graph)
		reads this`graph, this`NoEdge, this`numVertices, msg
	{
		isArray(msg) && isConsistentAt(vid, msg)
	}

	predicate isVertexAttr(vid: VertexId, attr: VertexAttr)
		requires isVertex(vid) && isMatrix(graph)
		reads this`graph, this`numVertices, this`NoEdge, this`Infinity, attr
	{
		isArray(attr)
		&&
		attr[vid] == 0
		&&
		forall i | 0 <= i < numVertices :: 0 <= attr[i] <= Infinity
		&&
		isConsistentAt(vid, attr)
	}

	predicate MsgInvariant(msgArray: array<Message>, active: array<bool>)
		requires isArray(msgArray) && isArray(active) && isMatrix(graph)
		reads this`graph, this`NoEdge, this`numVertices, active, msgArray, msgArray[..]
	{
		forall i | 0 <= i < numVertices :: active[i] ==> isMessageFor(msgArray[i], i)
	}

	predicate GraphInvariant0()
		requires isArray(vAttr)
		reads this`graph, this`vAttr, this`sent, this`numVertices, this`Infinity, vAttr, vAttr[..]
	{
		(forall i | 0 <= i < numVertices :: isArray(vAttr[i]))
			&& isMatrix(graph) && isMatrix(sent) && Infinity == numVertices + 1
	}

	predicate vAttrInvariant()
		requires isArray(vAttr) && GraphInvariant0()
		reads this`graph, this`vAttr, this`sent, this`numVertices, this`Infinity, vAttr, vAttr[..]
	{
		forall i,j | 0 <= i < numVertices && 0 <= j < numVertices :: 0 <= vAttr[i][j] <= Infinity
	}

	predicate GraphInvariant()
		requires isArray(vAttr)
		reads this`graph, this`vAttr, this`sent, this`numVertices, this`Infinity, vAttr, vAttr[..]
	{
		GraphInvariant0() && vAttrInvariant()
	}

	method Pregel(maxNumIterations: nat) returns (numIterations: nat)
		requires isArray(vAttr) && GraphInvariant0()
		requires numVertices > 1
		modifies vAttr, sent
		ensures GraphInvariant() && consistent()
		ensures numIterations < maxNumIterations ==> !active() && noCollisions()
	{
		numIterations := 0;
		
		InitializeVertices();

		while active() && numIterations < maxNumIterations
			invariant GraphInvariant() && consistent()
			invariant !active() ==> noCollisions()
		{
			var msg,active' := AggregateMessages();

			if active()
			{
				UpdateVertices(msg, active');
			}
						
			numIterations := numIterations + 1;
		}
	}

	method AggregateMessages() returns (msgArray: array<Message>, active: array<bool>)
		requires isArray(vAttr)
		requires GraphInvariant()
		requires consistent()
		modifies sent
		ensures noCollisions() && consistent()
		ensures fresh(msgArray) && fresh(active) && isArray(msgArray) && isArray(active)
		ensures MsgInvariant(msgArray, active)
	{
		// Dafny would have problems verifying this method if we made msg an in-parameter
		msgArray := new Message[numVertices];
		active := new bool[numVertices];
		forall i | 0 <= i < numVertices { active[i] := false; }
		assert forall i | 0 <= i < numVertices :: !active[i];

		var src' := 0;
		var srcIndices := Permutation.Generate(numVertices);
		// invoke SendMessage on each edge
		while src' < numVertices
			invariant src' <= numVertices
			invariant MsgInvariant(msgArray, active)
			invariant Permutation.isValid(srcIndices, numVertices)
			invariant forall i | 0 <= i < src' :: noCollisionsAt(srcIndices[i])
		{
			var src := srcIndices[src'];
			var dst' := 0;
			var dstIndices := Permutation.Generate(numVertices);
			while dst' < numVertices
				invariant dst' <= numVertices
				invariant src == srcIndices[src']
				invariant MsgInvariant(msgArray, active)
				invariant Permutation.isValid(srcIndices, numVertices)
				invariant Permutation.isValid(dstIndices, numVertices)
				invariant forall i | 0 <= i < dst' :: noCollisionBetween(src, dstIndices[i]);
				invariant forall i | 0 <= i < src' :: noCollisionsAt(srcIndices[i])
			{
				var dst := dstIndices[dst'];
				if adjacent(src, dst)
				{
					var msg' := SendMessage(src, dst, graph[src,dst]);
					AccumulateMessage(msgArray, msg', active);
				}
				//assert noCollisionBetween(src, dst);
				dst' := dst' + 1;
			}
			NoCollisionPermutationLemma1(src, dstIndices);
			//assert noCollisionsAt(src);
			src' := src' + 1;
		}
		NoCollisionPermutationLemma2(srcIndices);
		//assert noCollisions();
	}

	method AccumulateMessage(msgArray: array<Message>, msg': seq<(VertexId, Message)>, active: array<bool>)
		requires isMatrix(graph) && isArray(msgArray) && isArray(active)
		requires MsgInvariant(msgArray, active)
		requires forall m | m in msg' :: isVertex(m.0) && isMessageFor(m.1, m.0)
		modifies msgArray, active
		ensures MsgInvariant(msgArray, active)
	{
		var i := 0;
		while i < |msg'|
			invariant MsgInvariant(msgArray, active)
		{
			var m := msg'[i];
			if !active[m.0] {
				active[m.0] := true;
				msgArray[m.0] := m.1;
			} else {
				msgArray[m.0] := MergeMessage(msgArray[m.0], m.1);
			}
			assert isMessageFor(msgArray[m.0], m.0);
			i := i + 1;
		}
	}

	method InitializeVertices()
		requires isArray(vAttr)
		requires GraphInvariant0()
		requires numVertices > 0
		modifies vAttr, sent
		ensures GraphInvariant()
		ensures consistent()
		ensures active()
	{
		var vid := 0;
		while vid < numVertices
			invariant vid <= numVertices
			invariant GraphInvariant0()
			invariant isMatrix(sent) && vid > 0 ==> sent[0,0]
			invariant forall i | 0 <= i < vid :: isVertexAttr(i, vAttr[i])
		{
			vAttr[vid] := VertexProgram(vid, vAttr[vid], initMsg);
			assert isVertexAttr(vid, vAttr[vid]);
			sent[vid, vid] := true;
			vid := vid + 1;
		}
	}

	method UpdateVertices(msgArray: array<Message>, active: array<bool>)
		requires isArray(msgArray) && isArray(active) && isArray(vAttr)
		requires GraphInvariant()
		requires MsgInvariant(msgArray, active)
		requires consistent()
		modifies vAttr
		ensures GraphInvariant()
		ensures consistent()
	{
		var vid := 0;
		while vid < numVertices
			invariant GraphInvariant0() && vAttrInvariant()
			invariant consistent()
			invariant forall i | vid <= i < numVertices :: active[i] ==> isMessageFor(msgArray[i], i)
		{
			if active[vid] {
				vAttr[vid] := VertexProgram(vid, vAttr[vid], msgArray[vid]);
				assert isVertexAttr(vid, vAttr[vid]);
			}
			vid := vid + 1;
		}
	}

	method ResetSentMatrix()
		requires isMatrix(sent)
		modifies sent
		ensures !active()
	{
		var src := 0;
		while src < numVertices
			invariant src <= numVertices
			invariant forall i,j | 0 <= i < src && 0 <= j < numVertices :: !sent[i,j]
		{
			var dst := 0;
			while dst < numVertices
				invariant dst <= numVertices
				invariant forall j | 0 <= j < dst :: !sent[src,j]
				invariant forall i,j | 0 <= i < src && 0 <= j < numVertices :: !sent[i,j]
			{
				sent[src,dst] := false;
				dst := dst + 1;
			}
			src := src + 1;
		}
	}

	lemma NoCollisionPermutationLemma1(vid: VertexId, indices: array<VertexId>)
		requires isVertex(vid) && isArray(indices) && isArray(vAttr) && GraphInvariant0()
		requires Permutation.isValid(indices, numVertices)
		requires forall i :: 0 <= i < numVertices ==> noCollisionBetween(vid, indices[i])
		ensures noCollisionsAt(vid)
	{
		var i := 0;
		while i < numVertices
			invariant i <= numVertices;
			invariant Permutation.isValid(indices, numVertices)
			invariant forall j | 0 <= j < i :: noCollisionBetween(vid, j)
		{
			assert i in indices[..];
			assert noCollisionBetween(vid, i);
			i := i + 1;
		}
	}

	lemma NoCollisionPermutationLemma2(indices: array<VertexId>)
		requires isArray(indices) && isArray(vAttr) && GraphInvariant0()
		requires Permutation.isValid(indices, numVertices)
		requires forall i :: 0 <= i < numVertices ==> noCollisionsAt(indices[i])
		ensures noCollisions()
	{
		var i := 0;
		while i < numVertices
			invariant i <= numVertices;
			invariant Permutation.isValid(indices, numVertices)
			invariant forall j | 0 <= j < i :: noCollisionsAt(j)
		{
			assert i in indices[..];
			assert noCollisionsAt(i);
			i := i + 1;
		}
	}
}