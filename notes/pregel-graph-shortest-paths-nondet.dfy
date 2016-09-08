// RUN: %dafny /compile:0 /timeLimit:40 "%s" > "%t"

/**
 * This script tries to model and prove correctness of a fully-distributed Bellman-Ford algorithm:
 * https://github.com/apache/spark/blob/master/graphx/src/main/scala/org/apache/spark/graphx/lib/ShortestPaths.scala
 */

include "nondet-permutation.dfy"

type VertexId = int
type Distance = int
type Message = array<Distance>
type Weight = real

class PregelBellmanFordAlgorithm
{
	var numVertices: nat;
	var Infinity : nat;
	var graph: array2<Weight>;
	var vAttr : array2<VertexId>;
	var msg : array3<Distance>;
	var sent : array2<bool>;

	constructor (matrix: array2<Weight>)
		requires matrix != null && matrix.Length0 == matrix.Length1
		modifies this
		ensures GraphInvariant()
	{
		graph := matrix;
		var n := matrix.Length0;
		vAttr := new VertexId[n,n];
		sent := new bool[n,n];
		msg := new Distance[n,n,n];
		numVertices := n;
		Infinity := n + 1;
	}

	/**************************************
	 * Beginning of user-supplied functions
	 **************************************/

	method SendMessage(src: VertexId, dst: VertexId, w: Weight)
		requires isVertex(src) && isVertex(dst)
		requires GraphInvariant()
		requires MsgMatrixInvariant()
		requires vAttrInvariant()
		requires adjacent(src, dst)
		modifies msg, sent
		ensures noCollisionBetween(src, dst)
		ensures MsgMatrixInvariant()
		ensures vAttrInvariant()
	{
		sent[src,dst] := false;
		sent[dst,src] := false;
		var i := 0;
		while i < numVertices
			invariant i <= numVertices
			invariant (exists j | 0 <= j < i :: vAttr[src,j] > vAttr[dst,j] + 1) ==> sent[dst,src];
			invariant !(exists j | 0 <= j < i :: vAttr[src,j] > vAttr[dst,j] + 1) ==> !sent[dst,src];
		{
			if vAttr[src,i] > vAttr[dst,i] + 1
			{
				var j := 0;
				while j < numVertices
					invariant j <= numVertices
					invariant forall k | 0 <= k < j :: msg[dst,src,k] == vAttr[dst,k] + 1;
				{
					msg[dst,src,j] := vAttr[dst,j] + 1;
					j := j + 1;
				}
				sent[dst,src] := true;
				assert vAttr[src,i] > vAttr[dst,i] + 1; // needed by invariant
				assert forall k | 0 <= k < numVertices :: msg[dst,src,k] == vAttr[dst,k] + 1;
				break;
			}
			i := i + 1;
		}
		assert sent[dst,src] <==> exists j | 0 <= j < numVertices :: vAttr[src,j] > vAttr[dst,j] + 1;
	}

	method MergeMessage(msg: Message, msg': Message) returns (res: Message)
		requires isMessage(msg) && isMessage(msg')
		ensures fresh(res) && isMessage(res)
		ensures forall i | 0 <= i < numVertices :: res[i] == min(msg[i], msg'[i])
	{
		res := new Distance[numVertices];
		forall i | 0 <= i < numVertices {
			res[i] := min(msg[i], msg'[i]);
		}
	}

	method VertexProgram(vid: VertexId, msg: Message)
		requires isVertex(vid) && isMessage(msg)
		requires GraphInvariant()
		requires MsgInvariant(vid, msg)
		requires vAttrInvariant()
		requires noCollisions'()
		modifies vAttr
		ensures noCollisions'()
	{
		var vAttr' := new Distance[numVertices];
		forall i | 0 <= i < numVertices {
			vAttr'[i] := vAttr[vid,i];
		}
		assert forall i | 0 <= i < numVertices ::
			vAttr'[i] <= numVertices ==> connected'(vid, i, vAttr'[i]);

		var i := 0;
		while i < numVertices
			invariant i <= numVertices
			invariant forall i | 0 <= i < numVertices ::
				vAttr'[i] <= numVertices ==> connected'(vid, i, vAttr'[i])
			invariant forall i | 0 <= i < numVertices ::
				msg[i] <= numVertices ==> connected'(vid, i, msg[i])
			invariant forall j | 0 <= j < i :: vAttr[vid,j] == min(vAttr'[j], msg[j])
		{
			vAttr[vid,i] := min(vAttr'[i], msg[i]);
			i := i + 1;
		}
		assert forall dst | 0 <= dst < numVertices ::
			vAttr[vid,dst] <= numVertices ==> connected'(vid, dst, vAttr[vid,dst]);
	}

	/************************
	 * Correctness assertions
	 ************************/

	function method distancesComputed(): bool
		requires GraphInvariant()
		reads this`graph, this`msg, this`vAttr, this`sent, this`numVertices, this`Infinity
	{
		distancesComputed'(numVertices)
	}

	function method distancesComputed'(dist: nat): bool
		requires GraphInvariant()
		requires 0 <= dist < Infinity
		reads this`graph, this`msg, this`vAttr, this`sent, this`numVertices, this`Infinity
	{
		forall i,j | 0 <= i < numVertices && 0 <= j < numVertices ::
			((connectedWithin(i, j, dist) ==> 0 <= vAttr[i,j] <= dist)
			&&
			(vAttr[i,j] < Infinity ==> connected'(i, j, vAttr[i,j])))
	}

	lemma DistanceLemma()
		requires GraphInvariant()
		requires vAttrInvariant()
		requires noCollisions'()
		ensures !(exists i,j | 0 <= i < numVertices && 0 <= j < numVertices :: sent[i,j])
				&& noCollisionsInductive(numVertices, numVertices) ==> distancesComputed()
	{
		if !(exists i,j | 0 <= i < numVertices && 0 <= j < numVertices :: sent[i,j])
				&& noCollisionsInductive(numVertices, numVertices)
		{
			DistanceLemma'(numVertices);
		}
	}

	lemma DistanceLemma'(dist: nat)
		requires GraphInvariant()
		requires vAttrInvariant()
		requires noCollisions'()
		requires 0 <= dist < Infinity
		requires !(exists i,j | 0 <= i < numVertices && 0 <= j < numVertices :: sent[i,j])
		requires noCollisionsInductive(numVertices, numVertices)
		ensures distancesComputed'(dist)
	{
		if dist > 0
		{
			DistanceLemma'(dist - 1);

			var src := 0;
			while src < numVertices
				invariant src <= numVertices
				invariant forall i,j | 0 <= i < src && 0 <= j < numVertices :: connectedWithin(i, j, dist) ==> vAttr[i,j] <= dist
			{
				var dst := 0;
				while dst < numVertices
					invariant dst <= numVertices
					invariant forall j | 0 <= j < dst :: connected'(src, j, dist) ==> vAttr[src,j] <= dist
				{
					dst := dst + 1;
				}
				src := src + 1;
			}
		}
	}

	function method noCollisions'(): bool
		requires GraphInvariant()
		requires vAttrInvariant()
		reads this`graph, this`msg, this`vAttr, this`sent, this`numVertices, this`Infinity
	{
		//forall vid | 0 <= vid < numVertices :: noCollisionAt'(vid)
		forall src,dst | 0 <= src < numVertices && 0 <= dst < numVertices ::
			(vAttr[src,dst] <= numVertices ==> connected'(src, dst, vAttr[src,dst]))
	}

	function method noCollisionAt'(src: VertexId): bool
		requires isVertex(src)
		requires GraphInvariant()
		requires vAttrInvariant()
		reads this`graph, this`msg, this`vAttr, this`sent, this`numVertices, this`Infinity
	{
		forall dst | 0 <= dst < numVertices ::
			(vAttr[src,dst] <= numVertices ==> connected'(src, dst, vAttr[src,dst]))
	}

	method Validated(maxNumIterations: nat) returns (goal: bool)
		requires numVertices > 0
		requires GraphInvariant()
		modifies this`numVertices, vAttr, msg, sent
		ensures goal
	{
		var numIterations := Pregel(maxNumIterations);
		goal := numIterations <= maxNumIterations ==> distancesComputed();
	}

	/*******************************
	 * Correctness helper assertions
	 *******************************/

	function method noCollisions(): bool
		requires GraphInvariant()
		reads this`graph, this`msg, this`vAttr, this`sent, this`numVertices, this`Infinity
	{
		forall vid | 0 <= vid < numVertices :: noCollisionAt(vid)
	}

	function method noCollisionAt(src: VertexId): bool
		requires isVertex(src)
		requires GraphInvariant()
		reads this`graph, this`msg, this`vAttr, this`sent, this`numVertices, this`Infinity
	{
		forall dst | 0 <= dst < numVertices :: noCollisionBetween(src, dst)
	}

	function method noCollisionBetween(src: VertexId, dst: VertexId): bool
		requires isVertex(src) && isVertex(dst)
		requires GraphInvariant()
		reads this`graph, this`msg, this`vAttr, this`sent, this`numVertices, this`Infinity
	{
		(src == dst ==> vAttr[src,dst] == 0)
		&&
		(adjacent(src, dst) && !sent[src,dst] && !sent[dst,src] ==>
			forall i | 0 <= i < numVertices :: vAttr[src,i] <= vAttr[dst,i] + 1)
	}

	function method noCollisionsInductive(srcBound: VertexId, dstBound: VertexId): bool
		requires srcBound <= numVertices && dstBound <= numVertices
		requires GraphInvariant()
		reads this`graph, this`msg, this`vAttr, this`sent, this`numVertices, this`Infinity
	{
		forall src,dst | 0 <= src < srcBound && 0 <= dst < dstBound ::
			(src == dst ==> vAttr[src,dst] == 0)
			&&
			(adjacent(src, dst) && !sent[src,dst] && !sent[dst,src] ==>
				forall i | 0 <= i < numVertices :: vAttr[src,i] <= vAttr[dst,i] + 1)
	}

	lemma CollisionLemma()
		requires GraphInvariant()
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
				assert noCollisionAt(src);
				while dst < numVertices
					invariant dst <= numVertices
					invariant noCollisionsInductive(src, dst)
					invariant forall vid | 0 <= vid < dst ::
						(src == vid ==> vAttr[src,vid] == 0) &&
						(adjacent(src, vid) && !sent[src,vid] && !sent[vid,src] ==>
							forall i | 0 <= i < numVertices :: vAttr[src,i] <= vAttr[vid,i] + 1)
				{
					assert noCollisionBetween(src, dst);
					assert (src == dst ==> vAttr[src,dst] == 0) &&
							(adjacent(src, dst) && !sent[src,dst] && !sent[dst,src] ==>
								forall i | 0 <= i < numVertices :: vAttr[src,i] <= vAttr[dst,i] + 1);
					dst := dst + 1;
				}
				src := src + 1;
			}
		}
	}

	/******************
	 * Helper functions
	 ******************/

	function method active(): bool
		requires isMatrix(sent)
		reads this`sent, this`numVertices
	{
		exists i,j | 0 <= i < numVertices && 0 <= j < numVertices :: sent[i,j]
	}

	function method min(a: VertexId, b: VertexId): VertexId
	{
		if a >= b then b else a
	}

	function method adjacent(src: VertexId, dst: VertexId): bool
		requires isMatrix(graph) && isVertex(src) && isVertex(dst)
		reads this`graph, this`numVertices
	{
		graph[src,dst] != 0.0
	}

	/* Check if the distance between src and dst is dist. */
	function method hasDistance(src: VertexId, dst: VertexId, dist: nat): bool
		requires isMatrix(graph) && isVertex(src) && isVertex(dst)
		reads this`graph, this`numVertices
	{
		if dist == 0 then
			src == dst
		else
			connected'(src, dst, dist) && !connected'(src, dst, dist - 1)
	}

	/* Check if dst is reachable from src. */
	function method connected(src: VertexId, dst: VertexId): bool
		requires isMatrix(graph) && isVertex(src) && isVertex(dst)
		reads this`graph, this`numVertices
	{
		// exists dist :: 0 <= dist <= numVertices && connected'(src, dst, dist)
		connectedWithin(src, dst, numVertices)
	}

	/* Check if dst is reachable from src via a path with length <= dist. */
	function method connectedWithin(src: VertexId, dst: VertexId, dist: nat): bool
		requires isMatrix(graph) && isVertex(src) && isVertex(dst)
		reads this`graph, this`numVertices
	{
		exists d :: 0 <= d <= dist && connected'(src, dst, d)
	}

	/* Check if dst is reachable from src through a path of length dist. */
	function method connected'(src: VertexId, dst: VertexId, dist: int): bool
		requires isMatrix(graph) && isVertex(src) && isVertex(dst)
		reads this`graph, this`numVertices
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

	predicate isVertex(vid: VertexId)
		reads this`numVertices
	{
		0 <= vid < numVertices
	}

	predicate isMessage<T> (arr: array<T>)
		reads this`numVertices
	{
		arr != null && arr.Length == numVertices
	}

	predicate isMatrix<T> (mat: array2<T>)
		reads this`numVertices
	{
		mat != null && mat.Length0 == numVertices && mat.Length1 == numVertices
	}

	predicate isMatrix3D<T> (mat: array3<T>)
		reads this`numVertices
	{
		mat != null && mat.Length0 == numVertices && mat.Length1 == numVertices && mat.Length2 == numVertices
	}

	predicate isNonnegative (arr: array<Distance>)
		requires arr != null && arr.Length == numVertices
		reads this`numVertices, arr
	{
		forall i | 0 <= i < numVertices :: arr[i] >= 0
	}

	predicate GraphInvariant()
		reads this`graph, this`msg, this`vAttr, this`sent, this`numVertices, this`Infinity, this`Infinity
	{
		isMatrix(graph) && isMatrix(vAttr) && isMatrix(sent)
		&& isMatrix3D(msg) && Infinity == numVertices + 1
	}

	predicate vAttrInvariant()
		requires isMatrix(vAttr)
		reads this`vAttr, this`numVertices, this`Infinity
	{
		(forall i | 0 <= i < numVertices :: vAttr[i,i] == 0)
		&&
		(forall i,j | 0 <= i < numVertices && 0 <= j < numVertices :: 0 <= vAttr[i,j] <= Infinity)
	}

	predicate MsgMatrixInvariant()
		requires GraphInvariant()
		reads this`graph, this`msg, this`vAttr, this`sent, this`numVertices, this`Infinity
	{
		forall src,dst | 0 <= src < numVertices && 0 <= dst < numVertices ::
			(sent[dst,src] ==>
				(adjacent(src, dst) &&
				forall k | 0 <= k < numVertices :: msg[dst,src,k] == vAttr[dst,k] + 1))
	}

	predicate MsgInvariant(vid: VertexId, msg: array<Distance>)
		requires isVertex(vid) && isMessage(msg)
		requires isMatrix(vAttr) && isMatrix(graph)
		reads this`graph, this`vAttr, this`numVertices, msg
	{
		forall i | 0 <= i < numVertices ::
			exists v | 0 <= v < numVertices :: adjacent(vid, v) && msg[i] == vAttr[v,i] + 1
	}

	lemma MsgInvariantLemma(vid: VertexId, msg: array<Distance>, msg': array<Distance>)
		requires numVertices > 0
		requires isVertex(vid) && isMessage(msg) && isMessage(msg')
		requires isMatrix(vAttr) && isMatrix(graph)
		requires msg[..] == msg'[..]
		requires MsgInvariant(vid, msg)
		ensures MsgInvariant(vid, msg')
	{
		var i := 0;
		while i < numVertices
			invariant i <= numVertices
			invariant forall ii | 0 <= ii < i ::
				exists v | 0 <= v < numVertices :: adjacent(vid, v) && msg'[ii] == vAttr[v,ii] + 1
		{
			assert exists v | 0 <= v < numVertices :: adjacent(vid, v) && msg[i] == vAttr[v,i] + 1;
			var v :| 0 <= v < numVertices && adjacent(vid, v) && msg[i] == vAttr[v,i] + 1;
			assert 0 <= v < numVertices && adjacent(vid, v) && msg'[i] == vAttr[v,i] + 1;
			i := i + 1;
		}
		assert forall i | 0 <= i < numVertices ::
			exists v | 0 <= v < numVertices :: adjacent(vid, v) && msg'[i] == vAttr[v,i] + 1;
		assert MsgInvariant(vid, msg');
	}

	method MergeMessageInv(vid: VertexId, msg: Message, msg': Message) returns (res: Message)
		requires numVertices > 0
		requires isVertex(vid) && isMessage(msg) && isMessage(msg')
		requires isMatrix(vAttr) && isMatrix(graph)
		requires MsgInvariant(vid, msg) && MsgInvariant(vid, msg')
		ensures isMessage(res) && MsgInvariant(vid, res)
	{
		res := new Distance[numVertices];
		var i := 0;
		while i < numVertices
			invariant i <= numVertices
			invariant forall j | 0 <= j < i :: res[j] == min(msg[j], msg'[j])
			invariant MsgInvariant(vid, msg) && MsgInvariant(vid, msg')
			invariant forall j | 0 <= j < i ::
				exists v | 0 <= v < numVertices :: adjacent(vid, v) && res[j] == vAttr[v,j] + 1
		{
			var v  :| 0 <= v < numVertices && adjacent(vid, v) && msg[i] == vAttr[v,i] + 1;
			var v' :| 0 <= v' < numVertices && adjacent(vid, v') && msg'[i] == vAttr[v',i] + 1;
			res[i] := min(msg[i], msg'[i]);
			assert res[i] == msg[i] || res[i] == msg'[i];
			assert (0 <= v < numVertices && adjacent(vid, v) && res[i] == vAttr[v,i] + 1)
				|| (0 <= v' < numVertices && adjacent(vid, v') && res[i] == vAttr[v',i] + 1);
			assert exists v | 0 <= v < numVertices :: adjacent(vid, v) && res[i] == vAttr[v,i] + 1;
			i := i + 1;
		}
		assert forall i | 0 <= i < numVertices ::
				exists v | 0 <= v < numVertices :: adjacent(vid, v) && res[i] == vAttr[v,i] + 1;
		assert MsgInvariant(vid, res);
	}

	method {:verify false} Pregel(maxNumIterations: nat) returns (numIterations: nat)
		requires numVertices > 0
		requires GraphInvariant()
		modifies vAttr, msg, sent
		ensures numIterations <= maxNumIterations ==> distancesComputed()
	{
		var src := 0;
		while src < numVertices
			invariant src <= numVertices
			invariant forall i,j | 0 <= i < src && 0 <= j < numVertices :: vAttr[i,j] == if i == j then 0 else Infinity
		{
			var dst := 0;
			while dst < numVertices
				invariant dst <= numVertices
				invariant forall j | 0 <= j < dst :: vAttr[src,j] == if src == j then 0 else Infinity
				invariant forall i,j | 0 <= i < src && 0 <= j < numVertices :: vAttr[i,j] == if i == j then 0 else Infinity
			{
				vAttr[src,dst] := if src == dst then 0 else Infinity;
				dst := dst + 1;
			}
			src := src + 1;
		}
		sent[0,0] := true;
		assert sent[0,0]; // needed by the following assertion
		assert exists i,j | 0 <= i < numVertices && 0 <= j < numVertices :: sent[i,j];
		assert vAttrInvariant();
		assert noCollisions'();

		numIterations := 0;

		while (exists i,j | 0 <= i < numVertices && 0 <= j < numVertices :: sent[i,j]) && numIterations <= maxNumIterations
			invariant !(exists i,j | 0 <= i < numVertices && 0 <= j < numVertices :: sent[i,j]) ==> noCollisions()
			//invariant noCollisions'()
		{
			ResetSentMatrix();

			src := 0;
			/* invoke SendMessage on each edge */
			while src < numVertices
				invariant src <= numVertices
				invariant forall vid | 0 <= vid < src :: noCollisionAt(vid)
				//invariant noCollisions'()
			{
				var dst := 0;
				while dst < numVertices
					invariant dst <= numVertices
					invariant vAttrInvariant()
					//invariant noCollisions'()
					invariant forall vid | 0 <= vid < src :: noCollisionAt(vid)
					invariant forall vid | 0 <= vid < dst :: noCollisionBetween(src, vid)
				{
					if adjacent(src, dst)
					{
						SendMessage(src, dst, graph[src,dst]);
						//assert noCollisionBetween(src, dst);
					}
					//assert noCollisionBetween(src, dst);
					dst := dst + 1;
				}
				//assert noCollisionAt(src);
				src := src + 1;
			}
			assert noCollisions() && noCollisions'();

			var dstIndices := Permutation.Generate(numVertices);
			var srcIndices := Permutation.Generate(numVertices);

			var dstPointer := 0;
			while dstPointer < numVertices
				invariant dstPointer <= numVertices
				invariant Permutation.isValid(srcIndices, numVertices)
				invariant Permutation.isValid(dstIndices, numVertices)
			{
				var dst := dstIndices[dstPointer];
				/* Did some vertex send a message to dst? */
				if exists src' :: src' in srcIndices[..] && sent[src',dst]
				{
					var srcPointer := 0;
					var activated := false;
					var srcIndices' := srcIndices;
					var message: Message := new Distance[numVertices];
					var src' :| src' in srcIndices[..] && sent[src',dst];
					assert src' in srcIndices[..] && sent[src',dst];
					assert exists i | 0 <= i < numVertices :: srcIndices[i] == src';

					/* aggregate the messages sent to dst */
					while srcPointer < numVertices
						invariant srcPointer <= numVertices
						invariant isMessage(message)
						invariant Permutation.isValid(srcIndices, numVertices)
						invariant Permutation.isValid(dstIndices, numVertices)
						invariant 0 <= src' < numVertices && sent[src',dst]
						invariant srcIndices[..] == srcIndices'[..]
						invariant exists i | 0 <= i < numVertices :: srcIndices[i] == src'
						invariant (exists i | 0 <= i < srcPointer :: srcIndices[i] == src') ==> activated
						invariant activated ==> MsgInvariant(dst, message)
					{
						var src := srcIndices[srcPointer];
						if src == src'
						{	
							assert sent[src,dst];
							assert MsgMatrixInvariant();
							assert adjacent(dst, src);

							var message' := new Distance[numVertices];
							forall i | 0 <= i < numVertices {
								message'[i] := msg[src,dst,i];
							}

							assert MsgMatrixInvariant();
							assert forall dst,src | 0 <= dst < numVertices && 0 <= src < numVertices :: 
								(sent[src,dst] ==> (adjacent(dst, src) && forall k | 0 <= k < numVertices :: msg[src,dst,k] == vAttr[src,k] + 1));
							assert sent[src,dst] ==> forall k | 0 <= k < numVertices :: msg[src,dst,k] == vAttr[src,k] + 1;
							
							assert forall i | 0 <= i < numVertices :: msg[src,dst,i] == vAttr[src,i] + 1;
							assert forall i | 0 <= i < numVertices :: message'[i] == vAttr[src,i] + 1;
							assert forall i | 0 <= i < numVertices ::
								(exists vid | 0 <= vid < numVertices :: adjacent(dst, vid) && message'[i] == vAttr[vid,i] + 1);
							assert MsgInvariant(dst, message');

							if !activated
							{
								/* keep the first message as is */
								message := message';
								activated := true;
							} else {
								/* merge the new message with the old one */
								message := MergeMessageInv(dst, message, message');
							}
							assert MsgInvariant(dst, message);
						}
						srcPointer := srcPointer + 1;
					}
					assert MsgInvariant(dst, message);

					/* update vertex state according to the result of merges */
					VertexProgram(dst, message);
				}
				dstPointer := dstPointer + 1;
			}
			numIterations := numIterations + 1;
		}
		/* noCollisions() and !active() imply distancesComputed() */
		CollisionLemma();
		DistanceLemma();
	}

	method ResetSentMatrix()
		requires isMatrix(sent)
		modifies sent
		ensures forall i,j | 0 <= i < numVertices && 0 <= j < numVertices :: !sent[i,j]
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
}