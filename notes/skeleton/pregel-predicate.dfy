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

	predicate conflictsWith(src: VertexId, dst: VertexId)
		requires isVertex(src) && isVertex(dst)
		reads this`graph, this`sent, this`numVertices, this`vAttr, vAttr

	predicate consistent()
		requires isArray(vAttr) && GraphInvariant0()
		reads this`graph, this`vAttr, this`sent, this`numVertices, vAttr

	predicate isConsistentAt(vid: VertexId, attr: VertexAttr)
		requires  isMatrix(graph) && isVertex(vid)
		reads this`graph, this`numVertices

	predicate vAttrInvariant()
		requires isArray(vAttr) && GraphInvariant0()
		reads this`graph, this`sent, this`vAttr, vAttr, this`numVertices

	predicate isVertexAttr(vid: VertexId, attr: VertexAttr)
		requires isVertex(vid) && isMatrix(graph)
		reads this`graph, this`numVertices

	predicate isMessage(msg: Message)

	predicate isMessageFor(msg: Message, vid: VertexId)
		requires isVertex(vid) && isMatrix(graph)
		reads this`graph, this`numVertices
		ensures isMessage(msg)

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

	method AggregateMessages() returns (msgArray: array<Message>, active: array<bool>)
		requires isArray(vAttr)
		requires GraphInvariant()
		requires consistent()
		modifies sent
		ensures noCollisions() && consistent()
		ensures fresh(msgArray) && fresh(active) && isArray(msgArray) && isArray(active)
		ensures forall i | 0 <= i < numVertices :: active[i] ==> isMessageFor(msgArray[i], i)

	method AccumulateMessage(msgArray: array<Message>, msg': seq<(VertexId, Message)>, active: array<bool>)
		requires isArray(msgArray) && isArray(active) && isArray(vAttr)
		requires GraphInvariant()
		requires forall i | 0 <= i < numVertices :: active[i] ==> isMessageFor(msgArray[i], i)
		requires forall m | m in msg' :: isVertex(m.0) && isMessageFor(m.1, m.0)
		modifies msgArray, active
		ensures forall i | 0 <= i < numVertices :: active[i] ==> isMessageFor(msgArray[i], i)

	method InitializeVertices()
		requires isArray(vAttr)
		requires GraphInvariant0()
		requires numVertices > 0
		modifies vAttr, sent
		ensures GraphInvariant()
		ensures consistent()
		ensures active()

	method UpdateVertices(msgArray: array<Message>, active: array<bool>)
		requires isArray(msgArray) && isArray(active) && isArray(vAttr)
		requires GraphInvariant()
		requires forall i | 0 <= i < numVertices :: active[i] ==> isMessageFor(msgArray[i], i)
		requires consistent()
		modifies vAttr
		ensures GraphInvariant()
		ensures consistent()

	method ResetSentMatrix()
		requires isMatrix(sent)
		modifies sent
		ensures !active()

	//////////////////////////////////////////////////////////////////////////

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

	predicate GraphInvariant0()
		requires isArray(vAttr)
		reads this`graph, this`sent, this`vAttr, vAttr, this`numVertices
		{
			isMatrix(graph) && isMatrix(sent) && isArray(vAttr)
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
}