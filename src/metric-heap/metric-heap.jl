using DataStructures: BinaryHeap, extract_all!
import DataStructures: isempty
import Base.Order: lt

"""
    struct MetricHeapNode{T<:AbstractTableau}
        metricvalue::Int
        tableau::T
    end

The atomic element of a MetricHeap, it contains a tableau branch and a value for
the metric associated with the MetricHeap it is contained in.
"""
struct MetricHeapNode{T<:AbstractTableau}
    metricvalue::Int
    tableau::T

    function MetricHeapNode(
        metricvalue::Int,
        tableau::T
    ) where {
        T<:AbstractTableau
    }
        return new{T}(metricvalue, tableau)
    end

    function MetricHeapNode(
        metric::F,
        tableau::T
    ) where {
        F<:Function,
        T<:AbstractTableau
    }
        MetricHeapNode(metric(tableau), tableau)
    end
end

"""
    metricvalue(metricheapnode::MetricHeapNode)

Getter for the metric value of a heap node.
"""
metricvalue(metricheapnode::MetricHeapNode) = metricheapnode.metricvalue

"""
    tableau(metricheapnode::MetricHeapNode)

Getter for the tableau branch of a heap node.
"""
tableau(metricheapnode::MetricHeapNode) = metricheapnode.tableau

"""
    Base.show(io::IO, metricheapnode::MetricHeapNode)

A `MetricHeapNode` is represented as a tuple `(metricvalue, tableau)`.
"""
function Base.show(io::IO, metricheapnode::MetricHeapNode)
    print(
        io,
        "($(metricvalue(metricheapnode)), $(tableau(metricheapnode)))"
    )
end

"""
    struct MetricHeapOrdering <: Base.Order.Ordering end

Definition of a new ordering for the heaps treating them as min heaps ordered on
the metric value.
"""
struct MetricHeapOrdering <: Base.Order.Ordering end

"""
    lt(_::MetricHeapOrdering, a::MetricHeapNode, b::MetricHeapNode)

Definition of the lt function for the new ordering.
"""
function lt(_::MetricHeapOrdering, a::MetricHeapNode, b::MetricHeapNode)
    isless(metricvalue(a), metricvalue(b))
end

"""
    struct MetricHeap
        heap::BinaryHeap{MetricHeapNode}
        metric::Function
    end

A MetricHeap is basically a heap parametrized over a metric, i.e., a function
which extracts some information about a tableau branch, therefore containing in
each node a tableau branch and the relative value for the metric, and which is 
ordered as a min heap over this metric value.
"""
mutable struct MetricHeap{F<:Function}
    const metric::F
    heap::BinaryHeap{MetricHeapNode}

    function MetricHeap(
        metric::F,
        heap::BinaryHeap{MetricHeapNode}
    ) where {
        F<:Function
    }
        return new{F}(metric, heap)
    end

    function MetricHeap(metric::F) where {F<:Function}
        heap = BinaryHeap{MetricHeapNode}(MetricHeapOrdering())
        return MetricHeap(metric, heap)
    end
end

"""
    heap(metricheap::MetricHeap)

Getter for the binary heap of a MetricHeap.
"""
heap(metricheap::MetricHeap) = metricheap.heap

"""
    metric(metricheap::MetricHeap)

Getter for the metric function of a MetricHeap.
"""
metric(metricheap::MetricHeap) = metricheap.metric

"""
    push!(metricheap::MetricHeap, metricheapnode::MetricHeapNode)
    
Push new metricheapnode to a MetricHeap.
"""
function push!(metricheap::MetricHeap, metricheapnode::MetricHeapNode)
    push!(heap(metricheap), metricheapnode)
end

"""
    push!(metricheap::MetricHeap, tableau::T) where {T<:AbstractTableau}

Push new tableau to a MetricHeap.
"""
function push!(metricheap::MetricHeap, tableau::T) where {T<:AbstractTableau}
    push!(metricheap, MetricHeapNode(metric(metricheap), tableau))
end

"""
    pop!(metricheap::MetricHeap)

Pop head of a MetricHeap and return the tableau associated with it.
"""
pop!(metricheap::MetricHeap) = tableau(pop!(heap(metricheap)))

"""
    isempty(metricheap::MetricHeap)

Returns true if the MetricHeap is empty, false otherwise.
"""
isempty(metricheap::MetricHeap) = isempty(heap(metricheap))

"""
    cleanheaps!(metricheaps::Vector{MetricHeap})

Function to clean the `MetricHeap` removing all the nodes that have already been
expanded that are not leaves (as the latters correspond to an open fully
expanded branch, i.e., a satisfiable branch) or closed.
"""
function cleanheap!(metricheap::MetricHeap)
    nodes = extract_all!(metricheap.heap)
    deleteat!(
        nodes,
        findall(node->(expanded(node.tableau) && !isleaf(node.tableau)), nodes)
    )
    deleteat!(nodes, findall(node->closed(node.tableau), nodes))
    metricheap.heap = BinaryHeap{MetricHeapNode}(MetricHeapOrdering(), nodes)
end

"""
    cleanheaps!(metricheaps::Vector{MetricHeap})

Function to clean the `MetricHeap`s removing from all heaps all the nodes that
have already been expanded that are not leaves (as the latters correspond to an
open fully expanded branch, i.e., a satisfiable branch) or closed.
"""
function cleanheaps!(metricheaps::Vector{MetricHeap})
    for metricheap in metricheaps
        cleanheap!(metricheap)
    end
end

"""
    Base.show(io::IO, metricheap::MetricHeap)

A `MetricHeap` is represented by its `metric` and its `heap`.
"""
function Base.show(io::IO, metricheap::MetricHeap)
    print(
        io,
        "Metric: $(metric(metricheap))\nBinaryHeap: $(heap(metricheap).valtree)"
    )
end
