import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.ConcurrentModificationException;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Queue;
import java.util.Set;
import java.util.SortedSet;
import java.util.TreeSet;
import java.util.WeakHashMap;
import java.util.concurrent.atomic.AtomicBoolean;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.concurrent.atomic.AtomicLong;
import java.util.concurrent.atomic.AtomicMarkableReference;
import java.util.concurrent.locks.ReentrantReadWriteLock;
import java.util.function.Function;
import java.util.function.Predicate;
import java.util.function.Supplier;
import java.util.stream.Collectors;

/*
 * MIT License
 * Copyright (c) 2016 Eduardo Ribeiro Rodrigues
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
 * SOFTWARE.
 */

/**
 * <p>This class implements a dependency graph using a strongly connected
 * Directed Acyclic Graph (DAG) and allows sorting of its nodes in
 * topological order.</p>
 *
 * <p>Some important characteristics of this class are:</p>
 * <ol><li>The graph fully implements the {@link Collection} interface</li>
 * <li>Calling {@link #getTopology} will not destroy the graph: the same graph instance can be safely reused after a topological sort operation.</li>
 * <li>It can optionally be instantiated to be thread-safe (see {@link #DependencyGraph(boolean)}) adding some overhead due to use of {@link ReentrantReadWriteLock}s</li>
 * <li>It is capable of detecting cycles (or circular dependencies paths) and for each cycle list all participant nodes (see {@link #findCycles})</li></ol>
 *
 * @param <T> The content type for the graph
 * @author Eduardo Rodrigues (https://github.com/errodrigues/ez-graph)
 */
//TODO: implement new method iteratePathsBetween(a, b) returning a standard Iterator where each next entry will be a Collection representing one valid path between nodes a and b
public final class DependencyGraph<T> implements Collection<T> {
	private static final Predicate<Object> IS_NULL = o -> o == null;

	// stores all nodes in the graph
	private final Map<T, Node<T>> nodes = new HashMap<>();

	// stores only those nodes that do not have any incoming connections from
	// other nodes.
	private final Set<Node<T>> vertices = new HashSet<>();

	// stores only those nodes that do not have any outgoing connections to
	// other nodes.
	private final Set<Node<T>> dependentFree = new HashSet<>();

	// stores only those nodes that do have at least 1 outgoing AND 1 incoming connection to/from
	// other nodes.
	private final Set<Node<T>> bidirectionalNodes = new HashSet<>();

	// keeps count of the total number of edges (or connections), in or outbound
	private final AtomicInteger edges = new AtomicInteger(0);

	// sequence number used when creating new nodes
	private final AtomicInteger sequence = new AtomicInteger(0);
	private final AtomicLong version = new AtomicLong(0L);

	// indicates whether the graph should be thread-safe or not
	private final boolean threadSafe;
	// internal reentrant lock, used only in thread-safe mode
	private final ReentrantReadWriteLock lock;
	private final ThreadLocal<Boolean> mustLockForReadOnWriteUnlock;

	// caches the last topological sort result, while still valid
	private List<T> orderedListCache;
	// caches the cycles found since last call to findCycles
	private Collection<Collection<T>> foundCyclesCache;

	/**
	 * Construct a non-thread-safe graph
	 * @see #fluentBuilder()
	 */
	public DependencyGraph() {
		this(false);
	}

	/**
	 * Construct a non-thread-safe graph
	 *
	 * @param initialCapacity sets the initial capacity for some internal
	 * data structures.
	 */
	public DependencyGraph(final int initialCapacity) {
		this(initialCapacity, false);
	}

	/**
	 * Constructor
	 *
	 * @param ensureThreadSafe whether the graph must be thread-safe or not.
	 * Thread-safety will impact performance in some degree.
	 * @see #fluentThreadSafeBuilder()
	 */
	public DependencyGraph(final boolean ensureThreadSafe) {
		this.threadSafe = ensureThreadSafe;
		if (!this.threadSafe) {
			this.lock = null;
			this.mustLockForReadOnWriteUnlock = null;
		} else {
			this.lock = new ReentrantReadWriteLock();
			this.mustLockForReadOnWriteUnlock = new ThreadLocal<Boolean>() {
				@Override protected Boolean initialValue() {
					return Boolean.FALSE;
				}
			};
		}
	}

	/**
	 * Constructor
	 *
	 * @param initialCapacity sets the initial capacity for some internal
	 * data structures.
	 * @param ensureThreadSafe whether the graph must be thread-safe or not.
	 * Thread-safety will impact performance in some degree.
	 */
	public DependencyGraph(final int initialCapacity, final boolean ensureThreadSafe) {
		this.threadSafe = ensureThreadSafe;
		if (!this.threadSafe) {
			this.lock = null;
			this.mustLockForReadOnWriteUnlock = null;
		} else {
			this.lock = new ReentrantReadWriteLock();
			this.mustLockForReadOnWriteUnlock = new ThreadLocal<Boolean>() {
				@Override protected Boolean initialValue() {
					return Boolean.FALSE;
				}
			};
		}
	}

	private void mutateSafely(final Runnable mutationAction) {
		writeLockIfNeeded();
		try {
			mutationAction.run();
		} finally {
			writeUnlockIfNeeded();
		}
	}

	private <R> R mutateSafely(final Supplier<R> mutationAction) {
		writeLockIfNeeded();
		try {
			return mutationAction.get();
		} finally {
			writeUnlockIfNeeded();
		}
	}

	private void readSafely(final Runnable readingAction) {
		readLockIfNeeded();
		try {
			writeUnlockIfNeeded();
			readingAction.run();
		} finally {
			readUnlockIfNeeded();
		}
	}

	private <R> R readSafely(final Supplier<R> readingAction) {
		readLockIfNeeded();
		try {
			writeUnlockIfNeeded();
			return readingAction.get();
		} finally {
			readUnlockIfNeeded();
		}
	}

	/** @return New node with the given content */
	private Node<T> createNode(final T content) {
		return new Node<>(content, sequence.getAndIncrement());
	}

	@Override
	public int size() {
		return nodes.size();
	}

	/** Extracts the actual content from each Node in the given collection and collects the extracted content in another collection */
	private Collection<T> extractContent(final Collection<Node<T>> collection) {
		return collection.stream().map(node -> node.content).collect(Collectors.toList());
	}

	/**
	 * Identifies all the nodes that no other nodes depend on
	 * @return Collection of nodes that no other nodes depend on
	 */
	public Collection<T> getDependentFreeNodes() {
		return extractContent(dependentFree);
	}

	/**
	 * Identifies all the nodes that do not depend on any other node
	 * @return Collection of nodes that do not depend on any other node
	 */
	public Collection<T> getIndependentNodes() {
		return extractContent(vertices);
	}

	/**
	 * Add a node to the graph if and only if it is not already present in the graph, otherwise
	 * the content will be added again as a new graph node.
	 *
	 * @param content content to be added as a new node to the graph
	 */
	private boolean addNodeIfAbsent(final T content) {
		final Node<T> node = mutateSafely(() -> {
				if (!nodes.containsKey(content)) {
					final Node<T> n = createNode(content);
					nodes.put(content, n);
					markDirty();
					return n;
				}
				return null;
			});

		if (node != null) {
			initializeFor(node);
			return true;
		}

		return false;
	}

	private void initializeFor(final Node<T> node) {
		vertices.add(node);
		assert nodes.size() >= vertices.size() :
				"The number of sortedVertices should never be greater than total number of nodes";

		dependentFree.add(node);
		assert nodes.size() >= dependentFree.size() :
				"The number of dependent-free nodes should never be greater than total number of nodes";
	}

	/**
	 * Add new content to the graph, wrapped in a Node instance
	 * @param content content to be added as a new node to the graph
	 * @return new Node wrapping the added content
	 */
	private Node<T> addNode(final T content) {
		final Node<T> node = createNode(content);
		nodes.put(content, node);
		initializeFor(node);
		return node;
	}

	/**
	 * Add content to the graph as a new node only if the graph does not contain it yet.
	 * @param content non-null content to be added to the graph
	 * @throws NullPointerException if the given content is null
	 */
	@Override
	public boolean add(final T content) {
		ensureContentNotNull(content);
		return addNodeIfAbsent(content);
	}

	private void ensureContentNotNull(final Object... args) {
		for (final Object arg : args) {
			if (arg == null || arg instanceof Collection && ((Collection<?>) arg).stream().anyMatch(IS_NULL)) {
				throw new NullPointerException("Null content is not allowed");
			}
		}
	}

	/**
	 * <p>Adds 1 or more dependencies to the given dependent node.</p>
	 *
	 * <p>If the dependent content or any of the given dependencies don't exist
	 * as nodes in the graph, new nodes will automatically be created and added
	 * first.</p>
	 *
	 * <p>Because this is a strongly connected digraph,
	 * each new dependency will represent 2 new edges (or connections)
	 * between 2 nodes (dependent and dependency). For example, if A depends on B
	 * then B will have an outgoing connection to A as well as  A will have an
	 * incoming connection from B.</p>
	 *
	 * @param dependent The node that depends on each node provided in the
	 * dependencies collection
	 * @param dependencies All nodes that dependent depends on
	 * @throws NullPointerException if any of the arguments or any of the elements in &quot;dependencies&quot; is null
	 */
	public void addDependencies(final T dependent, final Collection<T> dependencies)
	{
		ensureContentNotNull(dependent, dependencies);
		mutateSafely(() -> {
			Node<T> to = nodes.get(dependent);
			boolean modified = false;
			boolean hasIncoming = false;

			if (to == null) {
				to = addNode(dependent);
				modified = true;
			} else {
				hasIncoming = to.hasIncoming();
				if (to.hasOutgoing() && !hasIncoming && !dependencies.isEmpty()) {
					final boolean added = bidirectionalNodes.add(to);
					assert added : dependent + " has outgoing but not incoming connections, hence it should NOT have been found in internal bidirectionalNodes set.";
				}
			}

			for (final T dep : dependencies) {
				Node<T> from = nodes.get(dep);
				if (from == null) {
					from = addNode(dep);
					modified = true;
				} else if (!from.hasOutgoing()) {
					final boolean removed = dependentFree.remove(from);
					assert removed : dep + " has no outgoing connections, hence it should have been found in internal dependentFree set.";
				}

				if (!hasIncoming) {
					final boolean removed = vertices.remove(to);
					assert removed : dependent + " has no incoming connections, hence it should have been found in internal sortedVertices set.";
					hasIncoming = true;
				}

				final boolean connectedOut = from.addOutgoing(to);
				final boolean connectedIn = to.addIncoming(from);

				if (connectedOut || connectedIn) {
					modified = true;
				}

				if (connectedOut && connectedIn) {
					edges.incrementAndGet();
				} else {
					assert connectedOut == connectedIn : String.format(
							"Found a previously existing illegal weak connection (one-way only) between %s and %s: %s -%s %s",
							dependent, dep, dependent, (connectedOut ? "<" : ">"), dep);
				}

				if (from.hasIncoming()) {
					bidirectionalNodes.add(from);
				}
			}

			if (modified) {
				markDirty();
			}
		});
	}

	/**
	 * <p>Convenience method equivalent to {@link #addConnections(Object, Collection)}</p>
	 * @param from The node that will be connected to each node provided in the given collection
	 * @param to All nodes that <strong>from</strong> will connect to
	 * @throws NullPointerException if &quot;from&quot; or any of the elements in &quot;to&quot; is null
	 */
	@SafeVarargs
	public final void addConnections(final T from, final T... to) {
		addConnections(from, Arrays.asList(to));
	}

	/**
	 * <p>Adds 1 or more connections from the given node.</p>
	 *
	 * <p>If the origin node or any of its given connections don't exist
	 * as nodes in the graph, new nodes will automatically be created and added
	 * first.</p>
	 *
	 * <p>Because this is a strongly connected digraph, each new connection will incur 2 new edges between both nodes
	 * being connected. For example, if A connects to B then A will have an outgoing connection to A as well as A will
	 * have an incoming connection from B.</p>
	 *
	 * @param from The node that will be connected to each node provided in the given collection
	 * @param to All nodes that <strong>from</strong> will connect to
	 * @throws NullPointerException if any of the arguments or any of the elements in &quot;to&quot; is null
	 */
	public void addConnections(final T from, final Collection<T> to) {
		ensureContentNotNull(from, to);
		mutateSafely(() -> {
			Node<T> fromNode = nodes.get(from);
			boolean modified = false;
			boolean hasOutgoing = false;

			if (fromNode == null) {
				fromNode = addNode(from);
				modified = true;
			} else {
				hasOutgoing = fromNode.hasOutgoing();
				if (fromNode.hasIncoming() && !hasOutgoing && !to.isEmpty()) {
					final boolean added = bidirectionalNodes.add(fromNode);
					assert added : from + " has incoming but not outgoing connections, hence it should NOT have been found in internal bidirectionalNodes set.";
				}
			}

			for (final T t : to) {
				Node<T> toNode = nodes.get(t);
				if (toNode == null) {
					toNode = addNode(t);
					modified = true;
				}

				if (!toNode.hasIncoming()) {
					final boolean removed = vertices.remove(toNode);
					assert removed : t + " has no incoming connections, hence it should have been found in internal sortedVertices set.";
				}

				if (!hasOutgoing) {
					final boolean removed = dependentFree.remove(fromNode);
					assert removed : from + " has no outgoing connections, hence it should have been found in internal dependentFree set.";
					hasOutgoing = true;
				}

				final boolean connectedOut = fromNode.addOutgoing(toNode);
				final boolean connectedIn = toNode.addIncoming(fromNode);

				if (connectedOut || connectedIn) {
					modified = true;
				}

				if (connectedOut && connectedIn) {
					edges.incrementAndGet();
				} else {
					assert connectedOut == connectedIn : String.format(
							"Found a previously existing illegal weak connection (one-way only) between %s and %s: %s -%s %s",
							from, t, from, (connectedOut ? ">" : "<"), t);
				}

				if (toNode.hasOutgoing()) {
					bidirectionalNodes.add(toNode);
				}
			}

			if (modified) {
				markDirty();
			}
		});
	}

	/**
	 * <p>Convenience method, equivalent to {@link #addDependencies(Object, Collection)}</p>
	 * @param dependent The node that depends on each node provided in the
	 * dependencies array
	 * @param dependencies Optional list of nodes that dependent depends on
	 * @throws NullPointerException if &quot;dependent&quot; or any of the elements in &quot;dependencies&quot; is null
	 */
	@SafeVarargs
	public final void addDependencies(final T dependent, final T... dependencies) {
		addDependencies(dependent, Arrays.asList(dependencies));
	}

	/**
	 * Convenience method, equivalent to {@link #removeDependencies(Object, Collection)}
	 * @param dependent The node that depends on each node provided in the
	 * dependencies array
	 * @param dependencies All nodes that should be removed as dependencies of
	 * the dependent node
	 */
	@SafeVarargs
	public final void removeDependencies(final T dependent, final T... dependencies) {
		ensureContentNotNull(dependent);
		removeDependencies(dependent, Arrays.asList(dependencies));
	}

	/**
	 * <p>Removes 1 or more dependencies from the given dependent node.</p>
	 *
	 * <p>Including nodes in the dependencies collection that are not connected to
	 * the dependent node won't have any effect.</p>
	 *
	 * <p>See method {@link #addDependencies(Object dependent, Collection)} for more details on some dependency
	 * internals.</p>
	 *
	 * @param dependent The node that depends on each node provided in the
	 * dependencies array
	 * @param dependencies All nodes that should be removed as dependencies of
	 * the dependent node
	 */
	public void removeDependencies(final T dependent, final Collection<T> dependencies) {
		ensureContentNotNull(dependent, dependencies);
		if (dependencies.isEmpty()) {
			return;
		}
		readSafely(() -> {
			final Node<T> to = nodes.get(dependent);
			if (to == null) {
				return;
			}
			mutateSafely(() -> {
				final AtomicBoolean modified = new AtomicBoolean(false);
				dependencies.stream().map(nodes::get).forEach(from -> {
					final boolean disconnectedOut = from.removeOutgoing(to);
					if (!from.hasOutgoing()) {
						dependentFree.add(from);
						bidirectionalNodes.remove(from);
					}
					final boolean disconnectedIn = to.removeIncoming(from);
					if (!to.hasIncoming()) {
						vertices.add(to);
						bidirectionalNodes.remove(to);
					}
					if (disconnectedIn || disconnectedOut) {
						modified.set(true);
						if (disconnectedIn && disconnectedOut) {
							edges.decrementAndGet();
						}
					}
				});
				if (modified.get()) {
					markDirty();
				}
			});
		});
	}

	/**
	 * Convenience method, equivalent to {@link #removeConnections(Object, Collection)}
	 * @param from The node that connects to each node provided in the
	 * &quot;to&quot; array
	 * @param to All nodes that should be disconnected
	 */
	@SafeVarargs
	public final void removeConnections(final T from, final T... to) {
		ensureContentNotNull(from);
		removeDependencies(from, Arrays.asList(to));
	}

	/**
	 * <p>Removes 1 or more connections from the given &quot;from&quot; node.</p>
	 *
	 * <p>Including nodes in the &quot;to&quot; collection that are not connected to
	 * the &quot;from&quot; node won't have any effect.</p>
	 *
	 * <p>See method {@link #addConnections(Object, Collection)} for more details.</p>
	 *
	 * @param from The node that connects to each node provided in the
	 * &quot;to&quot; array
	 * @param to All nodes that should be disconnected
	 */
	public void removeConnections(final T from, final Collection<T> to) {
		ensureContentNotNull(from, to);
		if (to.isEmpty()) {
			return;
		}
		readSafely(() -> {
			final Node<T> fromNode = nodes.get(from);
			if (fromNode == null) {
				return;
			}
			mutateSafely(() -> {
				final AtomicBoolean modified = new AtomicBoolean(false);
				to.stream().map(nodes::get).forEach(toNode -> {
					final boolean disconnectedIn = toNode.removeIncoming(fromNode);
					if (!toNode.hasIncoming()) {
						vertices.add(toNode);
						bidirectionalNodes.remove(toNode);
					}
					final boolean disconnectedOut = fromNode.removeOutgoing(toNode);
					if (!fromNode.hasOutgoing()) {
						dependentFree.add(fromNode);
						bidirectionalNodes.remove(fromNode);
					}
					if (disconnectedIn || disconnectedOut) {
						modified.set(true);
						if (disconnectedIn && disconnectedOut) {
							edges.decrementAndGet();
						}
					}
				});
				if (modified.get()) {
					markDirty();
				}
			});
		});
	}

	/**
	 * <p>Will remove the node containing the given content, if it exists in the graph.
	 * As a result, all edges directly connecting this node to other nodes will
	 * also be removed.</p>
	 *
	 * @param object The content to be removed from the graph
	 */
	@Override
	public boolean remove(final Object object) {
		ensureContentNotNull(object);
		return mutateSafely(() -> {
			final Node<T> node = nodes.remove(object);
			if (node != null) {
				edges.addAndGet(-node.countEdges());

				node.getOutgoingNodes().forEach(out -> {
					out.removeIncoming(node);
					if (!out.hasIncoming()) {
						vertices.add(out);
						bidirectionalNodes.remove(out);
					}
				});

				if (!node.hasIncoming()) {
					vertices.remove(node);
					bidirectionalNodes.remove(node);
				} else {
					node.getIncomingNodes().forEach(in -> {
						in.removeOutgoing(node);
						if (!in.hasOutgoing())
						{
							dependentFree.add(in);
							bidirectionalNodes.remove(in);
						}
					});
				}

				markDirty();
				return true;
			}
			return false;
		});
	}

	/**
	 * <p>Check if a given content exists in the graph</p>
	 *
	 * @param content Content to be verified
	 * @return true only if the given content exists in the graph
	 */
	public boolean contains(final Object content) {
		ensureContentNotNull(content);
		return readSafely(() -> nodes.containsKey(content));
	}

	/**
	 * Retrieves the contents of all nodes that the given content directly depends on.
	 *
	 * @param content The node to retrieve all direct dependencies from
	 * @return A collection containing all direct dependencies for the given content.
	 * If there aren't any, the collection will be empty.
	 */
	public Collection<T> getDirectDependencies(final T content) {
		return readSafely(() -> {
			final Node<T> node = nodes.get(content);
			if (node != null) {
				return Collections.unmodifiableCollection(node.getIncomingContent());
			}
			return Collections.emptyList();
		});
	}

	/**
	 * Retrieves the contents of all nodes that the given content is a direct
	 * dependency of.
	 *
	 * @param content The node to retrieve all direct dependents from
	 * @return A collection containing all direct dependents of the given content.
	 * If there aren't any, the collection will be empty.
	 */
	public Collection<T> getDirectDependents(final T content) {
		return readSafely(() -> {
			final Node<T> node = nodes.get(content);
			return node != null ? Collections.unmodifiableCollection(node.getOutgoingContent()) : Collections.emptyList();
		});
	}

	/** Helper class specialized in find paths between nodes in the graph */
	private final class PathFinder {
		private Snapshot snapshot = new Snapshot();

		private PathFinder() {
		}

		private void searchDepthFirst(final Node<T> node, final T target, final Deque<T> currentPath) {
			currentPath.add(node.content);
			if (node.content.equals(target)) {
				return;
			}
			for (final Node<T> next : snapshot.getAdjacentNodes(node)) {
				if (!currentPath.contains(next.content)) {
					searchDepthFirst(next, target, currentPath);
					if (target.equals(currentPath.peekLast())) {
						return;
					}
					currentPath.pollLast();
				}
			}
		}

		private Collection<T> findShortestPathBetween(final Node<T> node, final T target) {
			final Deque<T> shortestPath = new ArrayDeque<>();
			final Queue<Node<T>> queue = new ArrayDeque<>();
			for (Node<T> next = node; next != null; next = queue.poll()) {
				shortestPath.add(next.content);
				for (final Node<T> n : snapshot.getAdjacentNodes(next)) {
					if (n.content.equals(target)) {
						shortestPath.add(n.content);
						return shortestPath;
					}
					queue.offer(n);
				}
				if (shortestPath.size() > 1) {
					shortestPath.pollLast();
				}
			}
			shortestPath.clear();
			return shortestPath;
		}

		private Collection<T> findShortestPathBetween(final T a, final T b) {
			final Node<T> start = snapshot.nodes.get(a);
			if (start == null) {
				return Collections.emptyList();
			}
			return Collections.unmodifiableCollection(findShortestPathBetween(start, b));
		}
	}

	/** Helper class specialized in sorting the graph's content in topological order */
	private final class TopologicalSorter {
		/** Holds a snapshot of a graph node */
		private final class NodeSnapshot {
			private final Collection<Node<T>> inbound, outbound;

			private NodeSnapshot(final Node<T> node) {
				inbound = new HashSet<>(node.inbound.keySet());
				outbound = new HashSet<>(node.outbound.keySet());
			}
		}

		private final AtomicBoolean valid = new AtomicBoolean(true);
		private Map<T, Node<T>> nodes;
		private Map<Node<T>, NodeSnapshot> nodeSnapshots;
		private SortedSet<Node<T>> sortedVertices;
		private Integer edges;
		private Long version;

		private TopologicalSorter() {
			reset();
		}

		private void reset() {
			readSafely(() -> {
				version = DependencyGraph.this.version.get();
				edges = DependencyGraph.this.edges.get();
				nodes = new HashMap<>(DependencyGraph.this.nodes);
				nodeSnapshots = nodes.values().stream().collect(Collectors.toMap(Function.identity(), NodeSnapshot::new));
				sortedVertices = new TreeSet<>((a, b) -> {
					final Collection<Node<T>> incomingA = getIncomingNodes(a);
					final Collection<Node<T>> outgoingA = getOutgoingNodes(a);
					final Collection<Node<T>> outgoingB = getOutgoingNodes(b);
					return compareNodes(a.sequence, b.sequence, incomingA.size(), outgoingA.size(), outgoingB.size());
				});
				sortedVertices.addAll(DependencyGraph.this.vertices);
			});
			valid.set(true);
		}

		private boolean isNotStale() {
			return version != null && version.equals(DependencyGraph.this.version.get());
		}

		private Collection<Node<T>> getIncomingNodes(final Node<T> node) {
			final NodeSnapshot nodeSnapshot = nodeSnapshots.get(node);
			return nodeSnapshot != null ? nodeSnapshot.inbound : Collections.emptySet();
		}

		private Collection<Node<T>> getOutgoingNodes(final Node<T> node) {
			final NodeSnapshot nodeSnapshot = nodeSnapshots.get(node);
			return nodeSnapshot != null ? nodeSnapshot.outbound : Collections.emptySet();
		}

		private void discard() {
			version = null;
			nodes = null;
			sortedVertices = null;
			edges = null;
			nodeSnapshots = null;
		}

		private List<T> sort() {
			if (valid.compareAndSet(true, false)) {
				try {
					final List<T> result = new ArrayList<>(nodes.size());
					int edgesLeft = edges;

					Iterator<Node<T>> vertIter = sortedVertices.iterator();

					while (vertIter.hasNext()) {
						final Node<T> node = vertIter.next();
						vertIter.remove();

						result.add(node.content);

						final Iterator<Node<T>> outIter = getOutgoingNodes(node).iterator();
						while (outIter.hasNext()) {
							final Node<T> dependent = outIter.next();
							outIter.remove();
							edgesLeft--;

							final Collection<Node<T>> incoming = getIncomingNodes(dependent);
							incoming.remove(node);

							if (incoming.isEmpty()) {
								sortedVertices.add(dependent);
								vertIter = sortedVertices.iterator();
							}
						}
					}

					if (edgesLeft > 0) {
						throw new IllegalStateException("Circular dependency detected. You may call method findCycles to identify them.");
					}

					return Collections.unmodifiableList(result);
				} finally {
					discard();
				}
			} else {
				throw new IllegalStateException("Method sort() was called again on this instance without previous call to method reset().");
			}
		}
	}

	private static int compareNodes(final int sequenceA, final int sequenceB, final int incomingA, final int outgoingA, final int outgoingB) {
		int r = incomingA - outgoingB;
		if (r == 0) {
			r = outgoingB - outgoingA;
		}
		if (r == 0) {
			r = sequenceA - sequenceB;
		}
		return r;
	}

	/**
	 * <p>This method will perform a topological sorting of its content, based
	 * on the algorithm described by Arthur B. Kahn[1962] in article
	 * "Topological sorting of large networks", Communications of the ACM 5 (11): 558562</p>
	 *
	 * <p>During the sorting, if a directed cycle (or a circular reference) is
	 * detected, an IllegalStateException will be thrown.</p>
	 *
	 * <p>In order to be non-destructive and keep the graph reusable after this
	 * operation, this method will take snapshots of all required internal data structures
	 * and use them to perform the sorting.</p>
	 *
	 * <p>When running in thread-safe mode, this method will hold a read lock
	 * during the entire sort operation in order to avoid unpredicted results
	 * if the graph's contents were to be modified during the sorting.<p>
	 *
	 * @return A list containing the content of the graph in topological order.
	 * In other words, since this is a dependency graph, the elements of the list
	 * will be sorted in a correct and safe order of execution. If the graph is empty,
	 * then the resulting list will also be empty.
	 */
	public List<T> getTopology()
	{
		final List<T> cached = readSafely(() -> orderedListCache);
		if (cached != null) {
			return cached;
		}
		final TopologicalSorter topologicalSorter = new TopologicalSorter();
		final List<T> sortedList = topologicalSorter.sort();
		mutateSafely(() -> {
			if (topologicalSorter.isNotStale()) {
				orderedListCache = sortedList;
			}
		});
		return sortedList;
	}

	/**
	 * Finds shortest acyclic path between a and b. If cycles are found they will be ignored.
	 * @param a the starting node
	 * @param b the target node
	 * @return A collection containing the nodes representing the shortest acyclic path between a and b.
	 */
	public Collection<T> findShortestPathBetween(final T a, final T b) {
		ensureContentNotNull(a, b);
		return new PathFinder().findShortestPathBetween(a, b);
	}

	/** @return True if, and only if, this graph <strong>does not contain</strong> any cycles (circular dependencies) */
	public boolean isAcyclic() {
		return findCycles().isEmpty();
	}

	/** Helper class specialized in finding cycles (or circular dependencies) in the graph */
	private final class CycleFinder {
		private final Snapshot snapshot = new Snapshot();

		private CycleFinder() {
		}

		private Collection<Collection<T>> findCycles()
		{
			final Collection<Collection<T>> cycles = new HashSet<>();
			final Set<Node<T>> candidateCycleRoots = new HashSet<>(snapshot.bidirectionalNodes);
			Iterator<Node<T>> iter = candidateCycleRoots.iterator();
			while (iter.hasNext()) {
				try {
					findCycles(iter.next(), cycles, candidateCycleRoots);
				} catch (final ConcurrentModificationException ex) {
					iter = candidateCycleRoots.iterator();
				}
			}
			return Collections.unmodifiableCollection(cycles);
		}

		private boolean isNotStale() {
			return snapshot.isNotStale();
		}

		private void findCycles(final Node<T> root, final Collection<Collection<T>> cycles,
								final Set<Node<T>> candidateCycleRoots) {
			findCycles(root, root, new LinkedHashSet<>(), cycles, candidateCycleRoots);
		}

		private void findCycles(final Node<T> root, final Node<T> node, final LinkedHashSet<T> currentCycle,
								final Collection<Collection<T>> cycles, final Set<Node<T>> candidateCycleRoots)
		{
			if (node != root || currentCycle.isEmpty()) {
				if (currentCycle.contains(node.content)) {
					return;
				}

				currentCycle.add(node.content);
				snapshot.getOutgoingNodes(node).stream().filter(snapshot::hasOutgoing).forEachOrdered(out -> {
					if (snapshot.countEdges(out) == 2) {
						candidateCycleRoots.remove(out);
					}
					findCycles(root, out, currentCycle, cycles, candidateCycleRoots);
				});
//				currentCycle.remove(node.content);
			} else {
				//System.out.println("Found cycle: " + currentCycle);
				cycles.add(Collections.unmodifiableSet(currentCycle));
			}
		}
	}

	/**
	 * Identifies all cycles (circular paths) in the graph, if any.
	 *
	 * @return A collection of cycles. If there isn't any, the collection is empty, otherwise it will
	 * contain 1 or more collections, each one containing the graph nodes that
	 * participate in a circular dependency path.
	 */
	public Collection<Collection<T>> findCycles() {
		final Collection<Collection<T>> cached = readSafely(() -> foundCyclesCache);
		if (cached != null) {
			return cached;
		}
		final CycleFinder cycleFinder = new CycleFinder();
		final Collection<Collection<T>> cycles = cycleFinder.findCycles();
		mutateSafely(() -> {
			if (cycleFinder.isNotStale()) {
				foundCyclesCache = cycles;
			}
		});
		return cycles;
	}

	/**
	 * Clear the last cached topological sort.
	 */
	private void markDirty() {
		version.incrementAndGet();
		orderedListCache = null;
		foundCyclesCache = null;
	}

	/**
	 * Will hold the write lock if graph is running in thread-safe mode
	 * @see #DependencyGraph(boolean)
	 */
	private void writeLockIfNeeded() {
		if (threadSafe) {
			mustLockForReadOnWriteUnlock.set(readUnlockIfNeeded());
			lock.writeLock().lock();
		}
	}

	/**
	 * Will release the write lock if graph is running in thread-safe mode
	 * @see #DependencyGraph(boolean)
	 */
	private void writeUnlockIfNeeded() {
		if (isHoldingWriteLock()) {
			if (mustLockForReadOnWriteUnlock.get()) {
				lock.readLock().lock();
				mustLockForReadOnWriteUnlock.set(Boolean.FALSE);
			}
			lock.writeLock().unlock();
		}
	}

	/**
	 * Will hold the read lock if graph is running in thread-safe mode
	 * @see #DependencyGraph(boolean)
	 */
	private void readLockIfNeeded() {
		if (threadSafe) {
			lock.readLock().lock();
		}
	}

	/**
	 * Will release the read lock if graph is running in thread-safe mode
	 * @see #DependencyGraph(boolean)
	 */
	private Boolean readUnlockIfNeeded() {
		if (isHoldingReadLock()) {
			lock.readLock().unlock();
			return Boolean.TRUE;
		}
		return Boolean.FALSE;
	}

	private boolean isHoldingReadLock() {
		return threadSafe && lock.getReadHoldCount() > 0;
	}

	private boolean isHoldingWriteLock() {
		return threadSafe && lock.isWriteLockedByCurrentThread();
	}

	/** @throws NullPointerException if any of the content elements is null */
	@Override
	@SuppressWarnings("unchecked")
	public boolean addAll(final Collection<? extends T> content) {
		return operateOnAll(content, c -> add((T)c));
	}

	@Override
	public void clear() {
		mutateSafely(() -> {
			version.set(0L);
			sequence.set(0);
			nodes.clear();
			vertices.clear();
			dependentFree.clear();
			bidirectionalNodes.clear();
			edges.set(0);
			foundCyclesCache = null;
			orderedListCache = null;
		});
	}

	@Override
	public boolean containsAll(final Collection<?> content) {
		ensureContentNotNull(content);
		return readSafely(() -> nodes.keySet().containsAll(content));
	}

	@Override
	public boolean removeIf(final Predicate<? super T> filter) {
		return readSafely(() -> {
			final List<T> toRemove = nodes.keySet().stream().filter(filter).collect(Collectors.toList());
			if (!toRemove.isEmpty()) {
				return mutateSafely(() -> {
					final AtomicBoolean dirty = new AtomicBoolean(false);
					toRemove.forEach(c -> dirty.compareAndSet(false, remove(c)));
					if (dirty.get()) {
						markDirty();
						return true;
					}
					return false;
				});
			}
			return false;
		});
	}

	@Override
	public boolean isEmpty() {
		return readSafely(nodes::isEmpty);
	}

	/**
	 * {@inheritDoc}
	 * <p>The resulting Iterator will navigate all nodes in the graph, in no particular order,
	 * and it does not support the {@link java.util.Iterator#remove remove} operation.</p>
	 * @return {@inheritDoc}
	 */
	@Override
	public Iterator<T> iterator() {
		return readSafely(() -> Collections.unmodifiableSet(!threadSafe ? nodes.keySet() : new HashSet<>(nodes.keySet()))).iterator();
	}

	@Override
	public boolean removeAll(final Collection<?> content) {
		return operateOnAll(content, this::remove);
	}

	@Override
	public boolean retainAll(final Collection<?> content) {
		return operateOnAll(nodes.keySet(), n -> !content.contains(n) && remove(n));
	}

	private boolean operateOnAll(final Collection<?> content, final Function<Object, Boolean> operation) {
		ensureContentNotNull(content);
		return mutateSafely(() -> {
			final AtomicBoolean modified = new AtomicBoolean(false);
			content.forEach(c -> modified.compareAndSet(false, operation.apply(c)));
			if (modified.get()) {
				markDirty();
				return true;
			}
			return false;
		});
	}

	@Override
	public Object[] toArray() {
		final Object[] array = new Object[size()];
		return toArray(array);
	}

	@Override
	public <E> E[] toArray(final E[] array)
	{
		return readSafely(() -> nodes.keySet().toArray(array));
	}

	@SafeVarargs
	private static <T> Collection<T> union(final int capacity, final Collection<T> initial, final Collection<T>... others) {
		final Collection<T> union = new HashSet<>(capacity);
		union.addAll(initial);
		Arrays.stream(others).forEachOrdered(union::addAll);
		return union;
	}

	/**
	 * This helper class will take and hold a generic and immutable snapshot of the graph which can then be safely used by
	 * complex and/or time-consuming operations (such as traversals, sorting, etc.) without the need to lock the graph
	 * for other potential threads wanting to use it
	 */
	private final class Snapshot {
		/** Holds a snapshot of a graph node */
		private final class NodeSnapshot {
			private final Map<Node<T>, T> inbound, outbound;
			private Map<Node<T>, T> adjacents;

			private NodeSnapshot(final Node<T> node) {
				inbound = Collections.unmodifiableMap(new HashMap<>(node.inbound));
				outbound = Collections.unmodifiableMap(new HashMap<>(node.outbound));
			}
		}

		private final Map<T, Node<T>> nodes;
		private final Map<Node<T>, NodeSnapshot> nodeSnapshots;
		private final Set<Node<T>> vertices, bidirectionalNodes, dependentFree;
		private final Integer edges;
		private final Long version;

		/**
		 * Instantiating this class will immediately take a read-only snapshot of the entire graph.
		 * @apiNote Please use responsibly! Always try to keep snapshot instances as short-lived as possible to avoid
		 * excessive memory pressure or unwanted leaks.
		 */
		private Snapshot() {
			/** auxiliary data structure to allow multi-object return from lambda */
			final class Aux {
				private Map<T, Node<T>> nodes;
				private Map<Node<T>, NodeSnapshot> nodeSnapshots;
				private Set<Node<T>> vertices, bidirectionalNodes, dependentFree;
				private Integer edges;
				private Long version;
			}
			final Aux aux = new Aux();
			readSafely(() -> {
				aux.version = DependencyGraph.this.version.get();
				aux.nodes = Collections.unmodifiableMap(new HashMap<>(DependencyGraph.this.nodes));
				aux.vertices = Collections.unmodifiableSet(new HashSet<>(DependencyGraph.this.vertices));
				aux.bidirectionalNodes = Collections.unmodifiableSet(new HashSet<>(DependencyGraph.this.bidirectionalNodes));
				aux.dependentFree = Collections.unmodifiableSet(new HashSet<>(DependencyGraph.this.dependentFree));
				aux.edges = DependencyGraph.this.edges.get();
				aux.nodeSnapshots = aux.nodes.values().stream().collect(Collectors.toMap(Function.identity(), NodeSnapshot::new));
			});
			this.version = DependencyGraph.this.version.get();
			this.nodes = Collections.unmodifiableMap(new HashMap<>(DependencyGraph.this.nodes));
			this.vertices = Collections.unmodifiableSet(new HashSet<>(DependencyGraph.this.vertices));
			this.bidirectionalNodes = Collections.unmodifiableSet(new HashSet<>(DependencyGraph.this.bidirectionalNodes));
			this.dependentFree = Collections.unmodifiableSet(new HashSet<>(DependencyGraph.this.dependentFree));
			this.edges = DependencyGraph.this.edges.get();
			this.nodeSnapshots = this.nodes.values().stream().collect(Collectors.toMap(Function.identity(), NodeSnapshot::new));
		}

		private boolean isNotStale() {
			return version.equals(DependencyGraph.this.version.get());
		}

		private Map<Node<T>, T> getAdjacentsMap(final Node<T> node) {
			final NodeSnapshot nodeSnapshot = nodeSnapshots.get(node);
			if (nodeSnapshot == null) {
				return Collections.emptyMap();
			}
			if (nodeSnapshot.adjacents == null) {
				final Map<Node<T>, T> map = new HashMap<>(nodeSnapshot.inbound.size() + nodeSnapshot.outbound.size());
				nodeSnapshot.inbound.keySet().stream().collect(() -> map, (m, n) -> m.put(n, n.content), Map::putAll);
				nodeSnapshot.outbound.keySet().stream().collect(() -> map, (m, n) -> m.put(n, n.content), Map::putAll);
				nodeSnapshot.adjacents = Collections.unmodifiableMap(map);
			}
			return nodeSnapshot.adjacents;
		}

		private Collection<Node<T>> getIncomingNodes(final Node<T> node) {
			final NodeSnapshot nodeSnapshot = nodeSnapshots.get(node);
			return nodeSnapshot != null ? nodeSnapshot.inbound.keySet() : Collections.emptyList();
		}

		private Collection<T> getIncomingContent(final Node<T> node) {
			final NodeSnapshot nodeSnapshot = nodeSnapshots.get(node);
			return nodeSnapshot != null ? nodeSnapshot.inbound.values() : Collections.emptyList();
		}

		private Collection<Node<T>> getOutgoingNodes(final Node<T> node) {
			final NodeSnapshot nodeSnapshot = nodeSnapshots.get(node);
			return nodeSnapshot != null ? nodeSnapshot.outbound.keySet() : Collections.emptyList();
		}

		private Collection<T> getOutgoingContent(final Node<T> node) {
			final NodeSnapshot nodeSnapshot = nodeSnapshots.get(node);
			return nodeSnapshot != null ? nodeSnapshot.outbound.values() : Collections.emptyList();
		}

		private boolean hasOutgoing(final Node<T> node) {
			final NodeSnapshot nodeSnapshot = nodeSnapshots.get(node);
			return nodeSnapshot != null && !nodeSnapshot.outbound.isEmpty();
		}

		private boolean hasIncoming(final Node<T> node) {
			final NodeSnapshot nodeSnapshot = nodeSnapshots.get(node);
			return nodeSnapshot != null && !nodeSnapshot.inbound.isEmpty();
		}

		private int countEdges(final Node<T> node) {
			final NodeSnapshot nodeSnapshot = nodeSnapshots.get(node);
			return nodeSnapshot != null ? nodeSnapshot.inbound.size() + nodeSnapshot.outbound.size() : 0;
		}

		private Collection<Node<T>> getAdjacentNodes(final Node<T> node) {
			return getAdjacentsMap(node).keySet();
		}

		private Collection<T> getAdjacentContent(final Node<T> node) {
			return getAdjacentsMap(node).values();
		}
	}

	/**
	 * <p>Internal representation of a graph's node.</p>
	 * <p><strong>NOTE:</strong> Internal Nodes should remain internal, thus should never be exposed outside of the graph.</p>
	 * @param <C> The type of its content
	 */
	private final class Node<C> implements Comparable<Node<C>> {
		private final C content;
		private final int sequence;

		/*
		 * Since this class was designed to represent dependencies between elements,
		 * the direction of the relationships between graph nodes will follow the
		 * topological order. For example:
		 *
		 * If A depends on B, then:
		 *
		 * 1) B will have 1 outbound edge connecting to A
		 * 2) A will have 1 inbound edge connecting from B
		 */

		// let's be safe to avoid undesired leaks.
		private final WeakHashMap<Node<C>,C> inbound = new WeakHashMap<>();
		private final WeakHashMap<Node<C>,C> outbound = new WeakHashMap<>();

		/**
		 * Create a new node with the given content.
		 *
		 * @param content Content to store
		 * @param sequence The sequence in which the content is being added to
		 * the graph, which will be used as one of the criteria when comparing 2
		 * nodes in order to respect content addition order when sorting.
		 */
		private Node(final C content, final int sequence) {
			assert content != null : "Each node in a DependencyGraph must have a non-null content";
			assert sequence >= 0 : "Invalid negative sequence number";
			this.content = content;
			this.sequence = sequence;
		}

		/**
		 * Add 1 incoming connection from a given node to the current node
		 * @param node The origin of the incoming connection
		 */
		private boolean addIncoming(final Node<C> node) {
			return inbound.put(node, node.content) == null;
		}

		/**
		 * Remove the incoming connection from the given node to the current node
		 * @param node The origin of the incoming connection being be removed
		 */
		private boolean removeIncoming(final Node<C> node) {
			return inbound.remove(node) != null;
		}

		/**
		 * Add 1 outgoing connection from the current node to the given node
		 * @param node The target of the outgoing connection
		 */
		private boolean addOutgoing(final Node<C> node) {
			return outbound.put(node, node.content) == null;
		}

		/**
		 * Remove the outgoing connection from the current node to the given node
		 * @param node The target of the outgoing connection being be removed
		 */
		private boolean removeOutgoing(final Node<C> node) {
			return outbound.remove(node) != null;
		}

		/**
		 * Checks if the current node has any outgoing connections
		 * @return true only if the node has at least 1 outgoing connection to
		 * any other node
		 */
		private boolean hasOutgoing() {
			return !outbound.isEmpty();
		}

		private boolean hasOutgoingTo(final Node<C> node) {
			return outbound.containsKey(node);
		}

		/**
		 * Checks if the current node has any incoming connections
		 * @return true only if the node has at least 1 incoming connection from
		 * any other node
		 */
		private boolean hasIncoming() {
			return !inbound.isEmpty();
		}

		private boolean hasIncomingFrom(final Node<C> node) {
			return inbound.containsKey(node);
		}

		/**
		 * @return The origin nodes of all incoming connections to the current node
		 */
		private Collection<Node<C>> getIncomingNodes() {
			return inbound.keySet();
		}

		/**
		 * @return The target nodes of all outgoing connections from the current node
		 */
		private Collection<Node<C>> getOutgoingNodes()
		{
			return outbound.keySet();
		}

		/**
		 * Retrieve the contents of all origin nodes of all incoming connections
		 * to the current node.
		 * @return The contents of all origins of all incoming connections to the current node
		 */
		private Collection<C> getIncomingContent()
		{
			return inbound.values();
		}

		/**
		 * Retrieve the contents of all target nodes of all outgoing connections
		 * from the current node.
		 * @return The contents of all targets of all outgoing connections from the current node
		 */
		private Collection<C> getOutgoingContent() {
			return outbound.values();
		}

		private Collection<Node<C>> getAdjacentNodes() {
			return union(countEdges(), getIncomingNodes(), getOutgoingNodes());
		}

		private Collection<C> getAdjacentContent() {
			return union(countEdges(), getIncomingContent(), getOutgoingContent());
		}

		/**
		 * The sum of all incoming and outgoing connections for this node
		 * @return The total number of edges (or connections) for this node
		 */
		private int countEdges() {
			return inbound.size() + outbound.size();
		}

		/**
		 * <p>Will compare the current node with the given one using the following
		 * rules:</p>
		 *
		 * <p>Node A should come before B when</p>
		 * <ol>
		 * <li>A has less incoming connections (less dependencies) than B or</li>
		 * <li>A has more outbound connections (is a dependency to more nodes) than B or</li>
		 * <li>A's sequence number is minor than B's (A was added to the graph before B)</li>
		 * </ol>
		 *
		 * @param node The node to compare the current node with
		 * @return 0 (zero) if both nodes are actually the same node, negative
		 * if the current node is minor than node or positive if the current node is
		 * greater than node.
		 */
		public int compareTo(final Node<C> node) {
			return compareNodes(sequence, node.sequence, inbound.size(), outbound.size(), node.outbound.size());
		}

		/**
		 * A node is equal to another node if their contents are also equal.
		 * @param obj the node to compare with
		 * @return true only if both nodes are considered equal
		 */
		@Override
		@SuppressWarnings("unchecked")
		public boolean equals(final Object obj) {
			return obj instanceof Node && content.equals(((Node) obj).content);
		}

		/**
		 * Will return the hash code of the node's content
		 * @return The content's hash code
		 */
		@Override
		public int hashCode() {
			return content.hashCode();
		}

		/**
		 * A human readable representation of the node
		 * @return A human readable representation of the node
		 */
		@Override
		public String toString() {
			return "DependencyGraph.Node : " + content.toString();
		}
	}

	/**
	 * Returns a string representation of this collection.  The string
	 * representation consists of a list of the collection's elements in the
	 * order they are returned by its iterator, enclosed in square brackets
	 * (<tt>"[]"</tt>).  Adjacent elements are separated by the characters
	 * <tt>", "</tt> (comma and space).  Elements are converted to strings as
	 * by {@link String#valueOf(Object)}.
	 *
	 * @return a string representation of this collection
	 */
	public String toString() {
		final Iterator<T> it = iterator();
		if (!it.hasNext()) {
			return "[]";
		}

		final StringBuilder sb = new StringBuilder();
		sb.append('[');
		while (true) {
			final T e = it.next();
			sb.append(e);
			if (it.hasNext()) {
				sb.append(',').append(' ');
			} else {
				return sb.append(']').toString();
			}
		}
	}

	/**
	 * <p>Creates a new instance of {@link FluentBuilder} which can then be used to build a new graph by adding/connecting content.
	 * For example:</p>
	 *
	 * {@code final DependencyGraph<String> graph = DependencyGraph.<String>fluentThreadSafeBuilder().add("A").addConnections("A", "B", "C").addDependencies("B", "C", "D").addConnections("C", "E", "F").build();}
	 *
	 * @return New instance of {@link FluentBuilder}
	 * @see #DependencyGraph()
	 */
	public static <T> FluentBuilder<T> fluentBuilder() {
		return new FluentBuilder<>(new DependencyGraph<>());
	}

	/**
	 * <p>Equivalent to {@link #fluentBuilder()} but will build a thread-safe graph.</p>
	 * @return New instance of {@link FluentBuilder}
	 * @see #DependencyGraph(boolean)
	 */
	public static <T> FluentBuilder<T> fluentThreadSafeBuilder() {
		return new FluentBuilder<>(new DependencyGraph<>(true));
	}

	/**
	 * <p>Wraps the graph in a new instance of {@link FluentModifier} which can then be used to modify the graph
	 * by adding/connecting/removing content. For example:</p>
	 *
	 * {@code final DependencyGraph<String> graph = new DependencyGraph<>().fluentModifier().addConnections("A", "B", "C").addDependencies("B", "C", "D").remove("F").get();}
	 *
	 * @return New instance of {@link FluentModifier} wrapping the graph
	 */
	public FluentModifier<T> fluentModifier() {
		return new FluentModifier<>(this);
	}

	/**
	 * Internal interface specifying all public content-addition operations allowed on a graph
	 * @param <T> Content type
	 * @param <F> The concrete {@link AbstractFluent} type implementing this interface
	 */
	private interface FluentAddOperations<T, F extends AbstractFluent<T>> {
		/** @see DependencyGraph#add(Object) */
		F add(T content);
		/** @see DependencyGraph#addAll(Collection) */
		F addAll(Collection<? extends T> content);
		/** @see DependencyGraph#addDependencies(Object, Collection) */
		F addDependencies(T dependent, Collection<T> dependencies);
		/** @see DependencyGraph#addDependencies(Object, Object[])  */
		@SuppressWarnings("unchecked") F addDependencies(T dependent, T... dependencies);
		/** @see DependencyGraph#addConnections(Object, Collection) */
		F addConnections(T from, Collection<T> to);
		/** @see DependencyGraph#addConnections(Object, Object[]) */
		@SuppressWarnings("unchecked") F addConnections(T form, T... to);
	}

	/**
	 * Internal interface specifying all public content-removal operations allowed on a graph
	 * @param <T> Content type
	 * @param <F> The concrete {@link AbstractFluent} type implementing this interface
	 */
	private interface FluentRemoveOperations<T, F extends AbstractFluent<T>> {
		/** @see DependencyGraph#remove(Object) */
		F remove(Object content);
		/** @see DependencyGraph#removeAll(Collection) */
		F removeAll(Collection<?> content);
		/** @see DependencyGraph#removeIf(Predicate) */
		F removeIf(Predicate<? super T> test);
		/** @see DependencyGraph#retainAll(Collection) */
		F retainAll(Collection<?> content);
	}

	/**
	 * Base class for both {@link FluentBuilder} and {@link FluentModifier}
	 * @param <T> Content type
	 */
	private abstract static class AbstractFluent<T> {
		final AtomicMarkableReference<DependencyGraph<T>> graphRef = new AtomicMarkableReference<>(null, false);

		private AbstractFluent(final DependencyGraph<T> graph) {
			graphRef.set(graph, false);
		}

		private void validateState() {
			if (graphRef.isMarked()) {
				throw new IllegalStateException("This instance cannot be reused");
			}
		}

		final void markUnsable() {
			graphRef.set(null, true);
		}

		DependencyGraph<T> get() {
			validateState();
			return graphRef.getReference();
		}

		static <T, F extends AbstractFluent<T>> F add(final F fluent, final T content) {
			fluent.get().add(content);
			return fluent;
		}

		static <T, F extends AbstractFluent<T>> F addAll(final F fluent, final Collection<? extends T> content) {
			fluent.get().addAll(content);
			return fluent;
		}

		static <T, F extends AbstractFluent<T>> F addDependencies(final F fluent, final T dependent, final Collection<T> dependencies) {
			fluent.get().addDependencies(dependent, dependencies);
			return fluent;
		}

		@SafeVarargs
		static <T, F extends AbstractFluent<T>> F addDependencies(final F fluent, final T dependent, final T... dependencies) {
			fluent.get().addDependencies(dependent, dependencies);
			return fluent;
		}

		static <T, F extends AbstractFluent<T>> F addConnections(final F fluent, final T from, final Collection<T> to) {
			fluent.get().addConnections(from, to);
			return fluent;
		}

		@SafeVarargs
		static <T, F extends AbstractFluent<T>> F addConnections(final F fluent, final T from, final T... to) {
			fluent.get().addConnections(from, to);
			return fluent;
		}

		static <T, F extends AbstractFluent<T>> F remove(final F fluent, final Object content) {
			//noinspection SuspiciousMethodCalls
			fluent.get().remove(content);
			return fluent;
		}

		static <T, F extends AbstractFluent<T>> F removeAll(final F fluent, final Collection<?> content) {
			//noinspection SuspiciousMethodCalls
			fluent.get().removeAll(content);
			return fluent;
		}

		static <T, F extends AbstractFluent<T>> F removeIf(final F fluent, final Predicate<? super T> test) {
			fluent.get().removeIf(test);
			return fluent;
		}

		static <T, F extends AbstractFluent<T>> F retainAll(final F fluent, final Collection<?> content) {
			fluent.get().retainAll(content);
			return fluent;
		}
	}

	/**
	 * Convenience class to create and configure new {@link DependencyGraph} instances using fluent API.
	 * Method {@link #build()} should always be the last one in the fluent chain to provide the new graph just built.
	 * @param <T> The content type for the graph
	 */
	public static final class FluentBuilder<T> extends AbstractFluent<T> implements FluentAddOperations<T, FluentBuilder<T>> {
		private FluentBuilder(final DependencyGraph<T> graph) {
			super(graph);
		}

		/**
		 * @return The graph instance just built by this builder
		 * @apiNote This method should be called only once per builder instance as it will immediately become unusable after this method is called
		 * @throws IllegalStateException if this method is called more than once
		 */
		public DependencyGraph<T> build() {
			final DependencyGraph<T> graph = get();
			markUnsable();
			return graph;
		}

		/**
		 * @throws IllegalStateException if called after method {@link #build()} has been called once
		 */
		@Override
		public FluentBuilder<T> add(final T content) {
			return add(this, content);
		}

		/**
		 * @throws IllegalStateException if called after method {@link #build()} has been called once
		 */
		@Override
		public FluentBuilder<T> addAll(final Collection<? extends T> content) {
			return addAll(this, content);
		}

		/**
		 * @throws IllegalStateException if called after method {@link #build()} has been called once
		 */
		@Override
		public FluentBuilder<T> addDependencies(final T dependent, final Collection<T> dependencies) {
			return addDependencies(this, dependent, dependencies);
		}

		/**
		 * @throws IllegalStateException if called after method {@link #build()} has been called once
		 */
		@Override @SafeVarargs
		public final FluentBuilder<T> addDependencies(final T dependent, final T... dependencies) {
			return addDependencies(this, dependent, dependencies);
		}

		/**
		 * @throws IllegalStateException if called after method {@link #build()} has been called once
		 */
		@Override
		public FluentBuilder<T> addConnections(final T from, final Collection<T> to) {
			return addConnections(this, from, to);
		}

		/**
		 * @throws IllegalStateException if called after method {@link #build()} has been called once
		 */
		@Override @SafeVarargs
		public final FluentBuilder<T> addConnections(final T from, final T... to) {
			return addConnections(this, from, to);
		}
	}

	/**
	 * Convenience class to modify {@link DependencyGraph} instances using fluent API. Note that this class simply wraps
	 * the graph instance, hence all its operations will immediately affect the wrapped graph. Method {@link #get()} can
	 * be optionally called at the end of a call chain to simply return the wrapped graph.
	 * @param <T> The content type for the graph
	 */
	public static final class FluentModifier<T> extends AbstractFluent<T> implements FluentAddOperations<T, FluentModifier<T>>,
			FluentRemoveOperations<T, FluentModifier<T>> {

		private FluentModifier(final DependencyGraph<T> graph) {
			super(graph);
		}

		/** @return The graph instance wrapped by this modifier */
		@Override
		public DependencyGraph<T> get() {
			return super.get();
		}

		@Override
		public FluentModifier<T> add(final T content) {
			return add(this, content);
		}

		@Override
		public FluentModifier<T> addAll(final Collection<? extends T> content) {
			return addAll(this, content);
		}

		@Override
		public FluentModifier<T> addDependencies(final T dependent, final Collection<T> dependencies) {
			return addDependencies(this, dependent, dependencies);
		}

		@Override @SafeVarargs
		public final FluentModifier<T> addDependencies(final T dependent, final T... dependencies) {
			return addDependencies(this, dependent, dependencies);
		}

		@Override
		public FluentModifier<T> addConnections(final T from, final Collection<T> to) {
			return addConnections(this, from, to);
		}

		@Override @SafeVarargs
		public final FluentModifier<T> addConnections(final T from, final T... to) {
			return addConnections(this, from, to);
		}

		@Override
		public FluentModifier<T> remove(final Object content) {
			return remove(this, content);
		}

		@Override
		public FluentModifier<T> removeAll(final Collection<?> content) {
			return removeAll(this, content);
		}

		@Override
		public FluentModifier<T> removeIf(final Predicate<? super T> test) {
			return removeIf(this, test);
		}

		@Override
		public FluentModifier<T> retainAll(final Collection<?> content) {
			return retainAll(this, content);
		}
	}

//	public static void main(String[] args) {
//		final DependencyGraph<String> graph = DependencyGraph.<String>fluentThreadSafeBuilder()
//				.addConnections("A", "B", "C")
////				.addDependencies("B", "A")
////				.addDependencies("C", "A")
//				.addDependencies("B", "C", "D")
////				.addDependencies("E", "C")
////				.addDependencies("F", "C")
//				.addConnections("C", "E", "F")
//				.build();
//
//		System.out.println("Content: " + graph);
//		System.out.println("Acyclic: " + graph.isAcyclic());
//		System.out.println("Acyclic Paths: " + graph.findAllPathsBetween("A", "F"));
//		System.out.println("Shortest Path: " + graph.findShortestPathBetween("A", "F"));
//		try {
//			System.out.println("Topology: " + graph.getTopology());
//			graph.addConnections("C", "A");
////			graph.addDependencies("A", "C");
//			System.out.println("Shortest Path: " + graph.findShortestPathBetween("A", "F"));
//			System.out.println("Topology: " + graph.getTopology());
//		} catch (final IllegalStateException ex) {
//			ex.printStackTrace();
//			System.out.println("Cycles: " + graph.findCycles());
//		}
//	}
}
