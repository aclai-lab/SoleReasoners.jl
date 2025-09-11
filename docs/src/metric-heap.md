```@meta
CurrentModule = SoleReasoners
```

```@contents
Pages = ["metric-heap.md"]
```

# [Metric Heap](@id man-core)

The necessary components for the search strategies
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

```@docs
MetricHeapNode{T<:AbstractTableau}
metricvalue(metricheapnode::MetricHeapNode)
tableau(metricheapnode::MetricHeapNode)
Base.show(io::IO, metricheapnode::MetricHeapNode)
MetricHeapOrdering
lt(_::MetricHeapOrdering, a::MetricHeapNode, b::MetricHeapNode)
MetricHeap
heap(metricheap::MetricHeap)
metric(metricheap::MetricHeap)
push!(metricheap::MetricHeap, metricheapnode::MetricHeapNode)
push!(metricheap::MetricHeap, tableau::T) where {T<:AbstractTableau}
push!(
    metricheaps::Vector{MetricHeap},
    tableau::T
) where {
    T<:AbstractTableau
}
pop!(metricheap::MetricHeap)
isempty(metricheap::MetricHeap)
cleanheap!(metricheap::MetricHeap)
cleanheaps!(metricheaps::Vector{MetricHeap})
Base.show(io::IO, metricheap::MetricHeap)
```

## Metrics

Various `metric`s that can be used to create
`MetricHeap`s to ease the search of the expansion node on any tableau, such as
`randombranch` assigning a random weight to each node when pushing it into the
heaps, `distancefromroot` assignign to each node its distance from the root
giving priority to smaller distances (i.e., breadth-first search), or
`inversedistancefromroot`, giving priority to larger distances (i.e., a sort
of depth-first search).

`metric`s using specific fields of tableaux structures (e.g., `formula` for
`formulalength` for `PropositionalTableau`) can be found in the `metric.jl` file
of each subdirectory.

```@docs
randombranch(_::T) where {T<:AbstractTableau}
distancefromroot(t::T) where {T<:AbstractTableau}
inversedistancefromroot(t::T) where {T<:AbstractTableau}
formulaheight(t::T) where {T<:ManyValuedMultiModalTableau}
```

## Choosenode

Various policies to choose which
node to actually expand given the heads of the heaps (i.e., using a
`roundrobin!` policy, choosing each time the head of a different heap in a
sequential way, or `mostvoted!`, choosing the node that is the head of most
heaps).

Note that all policies are are signed as `!`, as they change the structures
(``popping'' elements from the heaps).

```@docs
roundrobin!(metricheaps::Vector{MetricHeap}, cycle::Int)
mostvoted!(metricheaps::Vector{MetricHeap}, args...)
```
