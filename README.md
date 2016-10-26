# ez-graph
A powerful yet easy to use dependency graph written in Java 8

This class implements a dependency graph using a strongly connected Directed Acyclic Graph (DAG) and allows sorting of its nodes in topological order.

## Some important characteristics of this class are:

1. The graph fully implements Java 8's Collection interface
2. It provides a standard Iterator and can be easily traversed in a simple for-each loop
3. Calling method getTopology will not destroy the graph so the same graph instance can be safely reused after a topological sort operation
4. It can optionally be instantiated to be thread-safe adding some overhead due to use of ReentrantReadWriteLock
5. It is capable of detecting cycles (or circular dependencies) and for each cycle list all participant nodes (see method findCycles)
6. Method findShortestPathBetween(a, b) will do extactly what it says using simple unweighted BFS (breadth-first search)

## To-do:

1. Implement new method iteratePathsBetween(a, b) returning a standard Iterator where each next entry will be a Collection of graph nodes representing one valid path between nodes a and b
