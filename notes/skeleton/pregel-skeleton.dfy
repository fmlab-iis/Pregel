include "nondet-permutation.dfy"

type VertexId = int
type EdgeAttr(==)
type VertexAttr
type Message

class PregelSkeleton
{
	var numVertices: nat;
	var initMsg: Message;
	var graph: array2<EdgeAttr>;
	var vAttr: array<VertexAttr>;
	var sent: array2<bool>;
	var NoEdge: EdgeAttr

	//////////////////////////////////////////////////////////////////////////

	method SendMessage(src: VertexId, dst: VertexId, w: EdgeAttr) returns (msg: seq<(VertexId, Message)>)
		requires isVertex(src) && isVertex(dst) && isArray(vAttr)
		requires GraphInvariant()
		requires consistent()
		requires adjacent(src, dst)
		modifies sent
		ensures consistent()
		ensures forall m | m in msg :: isVertex(m.0) && isMessageFor(m.1, m.0)
		ensures sent[src,dst] <==> conflictsWith(src, dst)
	
	method MergeMessageFor(vid: VertexId, msg: Message, msg': Message) returns (res: Message)
		requires isMatrix(graph) && isVertex(vid)
		requires isMessageFor(msg, vid) && isMessageFor(msg', vid)
		ensures isMessageFor(res, vid)

	method VertexProgram(vid: VertexId, attr: VertexAttr, msg: Message) returns (attr': VertexAttr)
		requires isVertex(vid) && isArray(vAttr) && GraphInvariant0()
		requires msg != initMsg ==> isVertexAttr(vid, attr)
		requires msg != initMsg ==> isMessageFor(msg, vid)
		ensures GraphInvariant0()
		ensures isVertexAttr(vid, attr') && isConsistentAt(vid, attr')

	//////////////////////////////////////////////////////////////////////////

	predicate conflictsWith(src: VertexId, dst: VertexId)
		requires isVertex(src) && isVertex(dst)
		reads this`graph, this`sent, this`numVertices, this`vAttr, vAttr

	predicate isConsistentAt(vid: VertexId, attr: VertexAttr)
		requires  isMatrix(graph) && isVertex(vid)
		reads this`graph, this`numVertices

	predicate isVertexAttr(vid: VertexId, attr: VertexAttr)
		requires isVertex(vid) && isMatrix(graph)
		reads this`graph, this`numVertices

	predicate isMessage(msg: Message)

	predicate isMessageFor(msg: Message, vid: VertexId)
		requires isVertex(vid) && isMatrix(graph)
		reads this`graph, this`numVertices
		ensures isMessage(msg)

	//////////////////////////////////////////////////////////////////////////

	method Validate()
		requires numVertices > 1
		requires isArray(vAttr) && GraphInvariant0()
		modifies this`numVertices, vAttr, sent
	{
		var maxNumIterations :| maxNumIterations > 0;
		var numIterations := Pregel(maxNumIterations);
		assert numIterations < maxNumIterations ==> !active() && noCollisions() && consistent();
	}

	function method active(): bool
		requires isMatrix(sent)
		reads this`sent, this`numVertices
	{
		exists i,j | 0 <= i < numVertices && 0 <= j < numVertices :: sent[i,j]
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

	predicate vAttrInvariant()
		requires isArray(vAttr) && GraphInvariant0()
		reads this`graph, this`sent, this`vAttr, vAttr, this`numVertices
	{
		forall vid | 0 <= vid < numVertices :: isVertexAttr(vid, vAttr[vid])
	}

	predicate GraphInvariant0()
		requires isArray(vAttr)
		reads this`graph, this`sent, this`numVertices, this`vAttr, vAttr
	{
		isMatrix(graph) && isMatrix(sent)
	}

	predicate GraphInvariant()
		requires isArray(vAttr)
		reads this`graph, this`sent, this`vAttr, vAttr, this`numVertices
	{
		GraphInvariant0() && vAttrInvariant()
	}

	function method adjacent(src: VertexId, dst: VertexId): bool
		requires isMatrix(graph) && isVertex(src) && isVertex(dst)
		reads this`graph, this`NoEdge, this`numVertices
	{
		graph[src,dst] != NoEdge
	}

	predicate consistent()
		requires isArray(vAttr) && GraphInvariant0()
		reads this`graph, this`vAttr, this`sent, this`numVertices, vAttr
	{
		forall vid | 0 <= vid < numVertices :: isConsistentAt(vid, vAttr[vid])
	}

	predicate noCollisions()
		requires isArray(vAttr) && GraphInvariant0()
		reads this`graph, this`NoEdge, this`sent, this`numVertices, this`vAttr, vAttr
	{
		forall vid | 0 <= vid < numVertices :: noCollisionsAt(vid)
	}

	predicate noCollisionsAt(src: VertexId)
		requires isVertex(src) requires isArray(vAttr) && GraphInvariant0()
		reads this`graph, this`NoEdge, this`sent, this`numVertices, this`vAttr, vAttr
	{
		forall dst | 0 <= dst < numVertices :: noCollisionBetween(src, dst)
	}

	predicate noCollisionBetween(src: VertexId, dst: VertexId)
		requires isVertex(src) && isVertex(dst) && isArray(vAttr) && GraphInvariant0()
		reads this`graph, this`NoEdge, this`sent, this`numVertices, this`vAttr, vAttr
	{
		adjacent(src, dst) && !sent[src,dst] && !sent[dst,src] ==> !conflictsWith(src, dst)
	}

	//////////////////////////////////////////////////////////////////////////

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

	//////////////////////////////////////////////////////////////////////////

	method AggregateMessages() returns (msgArray: array<Message>, active: array<bool>)
		requires isArray(vAttr)
		requires GraphInvariant()
		requires consistent()
		modifies sent
		ensures noCollisions() && consistent()
		ensures fresh(msgArray) && fresh(active) && isArray(msgArray) && isArray(active)
		ensures forall i | 0 <= i < numVertices :: active[i] ==> isMessageFor(msgArray[i], i)
	{
		msgArray := new Message[numVertices];
		active := new bool[numVertices];
		forall i | 0 <= i < numVertices { active[i] := false; }
		assert forall i | 0 <= i < numVertices :: !active[i];

		var src' := 0;
		var srcIndices := Permutation.Generate(numVertices);

		while src' < numVertices
			invariant src' <= numVertices
			invariant forall i | 0 <= i < numVertices :: active[i] ==> isMessageFor(msgArray[i], i)
			invariant Permutation.isValid(srcIndices, numVertices)
			invariant forall i | 0 <= i < src' :: noCollisionsAt(srcIndices[i])
		{
			var src := srcIndices[src'];
			var dst' := 0;
			var dstIndices := Permutation.Generate(numVertices);
			while dst' < numVertices
				invariant dst' <= numVertices
				invariant src == srcIndices[src']
				invariant forall i | 0 <= i < numVertices :: active[i] ==> isMessageFor(msgArray[i], i)
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
				assert noCollisionBetween(src, dst);
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
		requires forall i | 0 <= i < numVertices :: active[i] ==> isMessageFor(msgArray[i], i)
		requires forall m | m in msg' :: isVertex(m.0) && isMessageFor(m.1, m.0)
		modifies msgArray, active
		ensures forall i | 0 <= i < numVertices :: active[i] ==> isMessageFor(msgArray[i], i)
	{
		var i := 0;
		while i < |msg'|
			invariant forall i | 0 <= i < numVertices :: active[i] ==> isMessageFor(msgArray[i], i)
		{
			var m := msg'[i];
			if !active[m.0] {
				active[m.0] := true;
				msgArray[m.0] := m.1;
			} else {
				msgArray[m.0] := MergeMessageFor(m.0, msgArray[m.0], m.1);
				assert isMessageFor(msgArray[m.0], m.0);
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
			invariant forall i | 0 <= i < vid :: isConsistentAt(i, vAttr[i])
		{
			vAttr[vid] := VertexProgram(vid, vAttr[vid], initMsg);
			assert isVertexAttr(vid, vAttr[vid]) && isConsistentAt(vid, vAttr[vid]);
			sent[vid, vid] := true;
			vid := vid + 1;
		}
	}

	method UpdateVertices(msgArray: array<Message>, active: array<bool>)
		requires isArray(msgArray) && isArray(active) && isArray(vAttr)
		requires GraphInvariant() && vAttrInvariant()
		requires forall i | 0 <= i < numVertices :: active[i] ==> isMessageFor(msgArray[i], i)
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