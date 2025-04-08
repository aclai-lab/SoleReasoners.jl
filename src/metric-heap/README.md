# Metric Heap

This folder contains the necessary components for the search strategies
allowing for a ``smarter'' way of expanding the tableau tree structure,
aiming at finding a fully expanded open branch (resp. closing all branches)
in the fastest way possible.

A `MetricHeap` is basically a heap parametrized over a metric, i.e., a function
which extracts some information about a tableau branch, therefore containing in
each node a tableau branch and the relative value for the metric, and which is 
ordered as a min heap over this metric value.

Note that all `MetricHeap`s are ordered from the smaller value to the greatest,
and can contain negative values (all `Int`s)

Helpers to clear the heaps (e.g., to deallocate memory removing already expanded
non-leaf nodes and closed nodes) are also provided.

[metrics.jl](metrics.jl) contains various `metric`s that can be used to create
`MetricHeap`s to ease the search of the expansion node on any tableau, such as
`randombranch` assigning a random weight to each node when pushing it into the
heaps, `distancefromroot` assignign to each node its distance from the root
giving priority to smaller distances (i.e., breadth-first search), or
`inversedistancefromroot`, giving priority to larger distances (i.e., a sort
of depth-first search).

`metric`s using specific fields of tableaux structures (e.g., `formula` for
`formulalength` for `PropositionalTableau`) can be found in the `metric.jl` file
of each subdirectory.

[choose-node.jl](choose-node.jl) contains various policies to choose which
node to actually expand given the heads of the heaps (i.e., using a
`roundrobin!` policy, choosing each time the head of a different heap in a
sequential way, or `mostvoted!`, choosing the node that is the head of most
heaps).

Note that all policies are are signed as `!`, as they change the structures
(``popping'' elements from the heaps).
