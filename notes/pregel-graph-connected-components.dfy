/**
 * This script tries to model and prove correctness of
 * https://github.com/apache/spark/blob/master/graphx/src/main/scala/org/apache/spark/graphx/lib/ConnectedComponents.scala
 */

include "nondet-permutation.dfy"

type VertexId = int
type VertexAttr = int
type EdgeAttr = real
type Message = int

class PregelConnectedComponentMarkingAlgorithm
{
	var numVertices: nat;
	var initMsg: Message;
	var graph: array2<EdgeAttr>;
	var sent: array2<bool>;
	var vAttr: array<VertexAttr>;

	/**************************************
	 * Beginning of user-supplied functions
	 **************************************/

	method SendMessage(src: VertexId, dst: VertexId, w: EdgeAttr) returns (msg: seq<(VertexId, Message)>)
		requires isArray(vAttr) && isMatrix(sent) && isMatrix(graph)
		requires isVertex(src) && isVertex(dst)
		requires vAttrInvariant()
		requires adjacent(src, dst)
		modifies sent
		ensures noCollisionBetween(src, dst)
		ensures sent[src,dst] || sent[dst,src] <==> vAttr[src] != vAttr[dst];
		ensures forall m | m in msg :: isVertex(m.0) && isMessage(m.1)
	{
		if(vAttr[src] < vAttr[dst]) {
			sent[src,dst] := true;
			sent[dst,src] := false;
			msg := [(dst, vAttr[src])];
		} else
		if(vAttr[src] > vAttr[dst]) {
			sent[dst,src] := true;
			sent[src,dst] := false;
			msg := [(src, vAttr[dst])];
		} else {
			sent[src,dst] := false;
			sent[dst,src] := false;
			msg := [];
		}
	}

	function method MergeMessage(a: Message, b: Message): Message
	{
		if a <= b then a else b
	}

	method VertexProgram(vid: VertexId, attr: VertexAttr, msg: Message) returns (attr': VertexAttr)
		requires isVertex(vid)
		requires msg != initMsg ==> isMessage(msg)
		requires msg != initMsg ==> isVertexAttr(attr)
		ensures isVertexAttr(attr')
	{
		if msg == initMsg {
			attr' := vid;
		} else {
			attr' := attr;
		}
	}

	/************************
	 * Correctness assertions
	 ************************/

	function method correctlyColored(): bool
		requires 0 <= numVertices
		requires isArray(vAttr) && isMatrix(graph) && isMatrix(sent)
		reads vAttr, this`graph, this`vAttr, this`sent, this`numVertices
	{
		correctlyColored'(numVertices)
	}

	function method correctlyColored'(dist: VertexId): bool
		requires isArray(vAttr) && isMatrix(graph) && isMatrix(sent)
		requires 0 <= dist <= numVertices
		reads vAttr, this`graph, this`vAttr, this`sent, this`numVertices
	{
		forall i,j | 0 <= i < numVertices && 0 <= j < numVertices ::
			connected'(i, j, dist) ==> vAttr[i] == vAttr[j]
	}

	/*******************************
	 * Correctness helper assertions
	 *******************************/

	method Validate()
		requires numVertices > 1
		requires isArray(vAttr) && isMatrix(graph) && isMatrix(sent)
		modifies this`numVertices, vAttr, sent
	{
		var maxNumIterations :| maxNumIterations > 0;
		var numIterations := pregel(maxNumIterations);

		if numIterations < maxNumIterations {
			assert !active() && noCollisions();
			CollisionLemma();
			assert noCollisions'(numVertices, numVertices);
			ColoringLemma();
			assert correctlyColored();
		}
		assert numIterations < maxNumIterations ==> correctlyColored();
	}

	function method noCollisions(): bool
		requires isArray(vAttr) && isMatrix(graph) && isMatrix(sent)
		reads vAttr, this`graph, this`vAttr, this`sent, this`numVertices
	{
		forall vid :: 0 <= vid < numVertices ==> noCollisionAt(vid)
	}

	function method noCollisionAt(src: VertexId): bool
		requires isVertex(src) && isArray(vAttr) && isMatrix(graph) && isMatrix(sent)
		reads this`graph, this`sent, this`vAttr, this`numVertices, vAttr
	{
		forall dst :: 0 <= dst < numVertices ==> noCollisionBetween(src, dst)
	}

	function method noCollisionBetween(src: VertexId, dst: VertexId): bool
		requires isVertex(src) && isVertex(dst) && isArray(vAttr) && isMatrix(graph) && isMatrix(sent)
		reads this`graph, this`sent, this`vAttr, this`numVertices, vAttr
	{
		adjacent(src, dst) && !sent[src,dst] && !sent[dst,src] ==> vAttr[src] == vAttr[dst]
	}

	function method noCollisions'(srcBound: VertexId, dstBound: VertexId): bool
		requires srcBound <= numVertices && dstBound <= numVertices
		requires isArray(vAttr) && isMatrix(graph) && isMatrix(sent)
		reads vAttr, this`graph, this`vAttr, this`sent, this`numVertices
	{
		forall src,dst | 0 <= src < srcBound && 0 <= dst < dstBound ::
			adjacent(src, dst) && !sent[src,dst] && !sent[dst,src] ==> vAttr[src] == vAttr[dst]
	}

	lemma CollisionLemma()
		requires isArray(vAttr) && isMatrix(graph) && isMatrix(sent)
		ensures noCollisions() ==> noCollisions'(numVertices, numVertices)
	{
		if noCollisions()
		{
			var src := 0;
			while src < numVertices
				invariant src <= numVertices
				invariant noCollisions'(src, numVertices)
			{
				var dst := 0;
				assert noCollisionAt(src);
				while dst < numVertices
					invariant dst <= numVertices
					invariant noCollisions'(src, dst)
					invariant forall vid :: 0 <= vid < dst ==>
						(adjacent(src, vid) && !sent[src,vid] && !sent[vid,src] ==> vAttr[src] == vAttr[vid])
				{
					assert noCollisionBetween(src, dst);
					assert adjacent(src, dst) && !sent[src,dst] && !sent[dst,src] ==> vAttr[src] == vAttr[dst];
					dst := dst + 1;
				}
				src := src + 1;
			}
		}
	}

	lemma ColoringLemma()
		requires isArray(vAttr) && isMatrix(graph) && isMatrix(sent)
		ensures !(exists i,j | 0 <= i < numVertices && 0 <= j < numVertices :: sent[i,j])
				&& noCollisions'(numVertices, numVertices) ==> correctlyColored()
	{
		if !(exists i,j | 0 <= i < numVertices && 0 <= j < numVertices :: sent[i,j])
				&& noCollisions'(numVertices, numVertices)
		{
			ColoringLemma'(numVertices);
		}
	}

	lemma ColoringLemma'(dist: nat)
		requires 0 <= dist <= numVertices
		requires isArray(vAttr) && isMatrix(graph) && isMatrix(sent)
		requires !(exists i,j | 0 <= i < numVertices && 0 <= j < numVertices :: sent[i,j])
		requires noCollisions'(numVertices, numVertices)
		ensures correctlyColored'(dist)
	{
		if dist > 1 { ColoringLemma'(dist - 1); }
	}

	/******************
	 * Helper functions
	 ******************/

	/* Cannot use this predicate due to Dafny's bug (https://dafny.codeplex.com/workitem/146). */
	function method active(): bool
		requires isMatrix(sent)
		reads this`sent, this`numVertices
	{
		exists i,j | 0 <= i < numVertices && 0 <= j < numVertices :: sent[i,j]
	}

	function method adjacent(src: VertexId, dst: VertexId): bool
		requires isMatrix(graph) && isVertex(src) && isVertex(dst)
		reads this`graph, this`numVertices
	{
		graph[src,dst] != 0.0
	}

	function method connected(src: VertexId, dst: VertexId): bool
		requires isMatrix(graph) && isVertex(src) && isVertex(dst)
		reads this`graph, this`numVertices
	{
		exists dist | 1 <= dist <= numVertices :: connected'(src, dst, dist)
	}

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

	predicate isMessage(msg: Message)
		reads this`numVertices
	{
		isVertex(msg)
	}

	predicate isVertexAttr(attr: VertexAttr)
		reads this`numVertices
	{
		isVertex(attr)
	}

	predicate vAttrInvariant()
		requires isArray(vAttr)
		reads this`vAttr, this`numVertices, vAttr
	{
		forall i | 0 <= i < numVertices :: isVertexAttr(vAttr[i])
	}

	method pregel(maxNumIterations: nat) returns (numIterations: nat)
		requires numVertices > 1 && maxNumIterations > 0
		requires isArray(vAttr) && isMatrix(graph) && isMatrix(sent)
		modifies vAttr, sent
		ensures numIterations < maxNumIterations ==> !active() && noCollisions()
	{
		InitializeVertices();

		numIterations := 0;

		while (exists i,j | 0 <= i < numVertices && 0 <= j < numVertices :: sent[i,j]) && numIterations < maxNumIterations
			invariant !(exists i,j | 0 <= i < numVertices && 0 <= j < numVertices :: sent[i,j]) ==> noCollisions()
			invariant vAttrInvariant()
		{
			var msg,active' := AggregateMessages();

			if exists i,j :: 0 <= i < numVertices && 0 <= j < numVertices && sent[i,j]
			{
				ghost var src',dst' :| 0 <= src' < numVertices && 0 <= dst' < numVertices && sent[src',dst'];

				UpdateVertices(msg, active');

				assert vAttrInvariant();
				assert 0 <= src' < numVertices && 0 <= dst' < numVertices && sent[src',dst'];
			}
			numIterations := numIterations + 1;
		}
		assert numIterations < maxNumIterations ==> !active();
		assert !active() ==> noCollisions();
	}

	method AggregateMessages() returns (msg: array<Message>, active: array<bool>)
		requires isArray(vAttr) && isMatrix(graph) && isMatrix(sent)
		requires vAttrInvariant()
		modifies sent
		//ensures vAttrInvariant()
		ensures noCollisions()
		ensures fresh(msg) && fresh(active) && isArray(msg) && isArray(active)
		ensures forall i | 0 <= i < numVertices :: active[i] ==> isMessage(msg[i])
	{
		// Dafny would have problems verifying this method if we made msg an in-parameter
		msg := new Message[numVertices];
		active := new bool[numVertices];
		forall i | 0 <= i < numVertices { active[i] := false; }
		assert forall i | 0 <= i < numVertices :: !active[i];

		var src' := 0;
		var srcIndices := Permutation.Generate(numVertices);
		// invoke SendMessage on each edge
		while src' < numVertices
			invariant src' <= numVertices
			invariant Permutation.isValid(srcIndices, numVertices)
			invariant forall i | 0 <= i < src' :: noCollisionAt(srcIndices[i])
			invariant forall i | 0 <= i < numVertices :: active[i] ==> isMessage(msg[i])
		{
			var src := srcIndices[src'];
			var dst' := 0;
			var dstIndices := Permutation.Generate(numVertices);
			while dst' < numVertices
				invariant dst' <= numVertices
				invariant src == srcIndices[src']
				invariant Permutation.isValid(srcIndices, numVertices)
				invariant Permutation.isValid(dstIndices, numVertices)
				invariant forall i | 0 <= i < dst' :: noCollisionBetween(src, dstIndices[i]);
				invariant forall i | 0 <= i < src' :: noCollisionAt(srcIndices[i])
				invariant forall i | 0 <= i < numVertices :: active[i] ==> isMessage(msg[i])
			{
				var dst := dstIndices[dst'];
				if adjacent(src, dst)
				{
					var msg' := SendMessage(src, dst, graph[src,dst]);
					AccumulateMessage(msg, msg', active);
				}
				//assert noCollisionBetween(src, dst);
				dst' := dst' + 1;
			}
			NoCollisionPermutationLemma1(src, dstIndices);
			//assert noCollisionAt(src);
			src' := src' + 1;
		}
		NoCollisionPermutationLemma2(srcIndices);
		//assert noCollisions();
	}

	method AccumulateMessage(msg: array<Message>, msg': seq<(VertexId, Message)>, active: array<bool>)
		requires isArray(msg) && isArray(active) && isArray(vAttr)
		requires forall m | m in msg' :: isVertex(m.0) && isMessage(m.1)
		requires forall i | 0 <= i < numVertices :: active[i] ==> isMessage(msg[i])
		modifies msg, active
		ensures forall i | 0 <= i < numVertices :: active[i] ==> isMessage(msg[i])
	{
		var i := 0;
		while i < |msg'|
			invariant forall i | 0 <= i < numVertices :: active[i] ==> isMessage(msg[i])
		{
			var m := msg'[i];
			if active[m.0] {
				active[m.0] := true;
				msg[m.0] := m.1;
			} else {
				msg[m.0] := MergeMessage(msg[m.0], m.1);
			}
			i := i + 1;
		}
	}

	method InitializeVertices()
		requires isArray(vAttr) && isMatrix(graph) && isMatrix(sent)
		requires numVertices > 0
		modifies vAttr, sent
		ensures vAttrInvariant()
		ensures active()
	{
		var vid := 0;
		while vid < numVertices
			invariant vid <= numVertices
			invariant isMatrix(sent) && vid > 0 ==> sent[0,0]
			invariant forall i | 0 <= i < vid :: isVertexAttr(vAttr[i])
		{
			vAttr[vid] := VertexProgram(vid, vAttr[vid], initMsg);
			sent[vid, vid] := true;
			vid := vid + 1;
		}
	}

	method UpdateVertices(msg: array<Message>, active: array<bool>)
		requires isArray(msg) && isArray(active) && isArray(vAttr)
		requires vAttrInvariant()
		requires forall i | 0 <= i < numVertices :: active[i] ==> isMessage(msg[i])
		modifies vAttr
		ensures vAttrInvariant()
	{
		var vid := 0;
		while vid < numVertices
			invariant vAttrInvariant()
			invariant forall i | 0 <= i < numVertices :: active[i] ==> isMessage(msg[i])
		{
			if active[vid] {
				vAttr[vid] := VertexProgram(vid, vAttr[vid], msg[vid]);
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
		requires isVertex(vid) && isArray(indices) && isArray(vAttr) && isMatrix(graph) && isMatrix(sent)
		requires Permutation.isValid(indices, numVertices)
		requires forall i :: 0 <= i < numVertices ==> noCollisionBetween(vid, indices[i])
		ensures noCollisionAt(vid)
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
		requires isArray(indices) && isArray(vAttr) && isMatrix(graph) && isMatrix(sent)
		requires Permutation.isValid(indices, numVertices)
		requires forall i :: 0 <= i < numVertices ==> noCollisionAt(indices[i])
		ensures noCollisions()
	{
		var i := 0;
		while i < numVertices
			invariant i <= numVertices;
			invariant Permutation.isValid(indices, numVertices)
			invariant forall j | 0 <= j < i :: noCollisionAt(j)
		{
			assert i in indices[..];
			assert noCollisionAt(i);
			i := i + 1;
		}
	}
}