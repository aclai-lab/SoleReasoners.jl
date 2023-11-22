module Reasoners

export sat

using SoleLogics
using DataStructures
using StatsBase

struct TableauNode
    φ::Formula
    children::Union{TableauNode,Nothing}

    function TableauNode(φ::Formula, children::Union{TableauNode, Nothing})
        return new(φ, children)
    end

    function TableauNode(φ::Formula)
        return TableauNode(φ, nothing)
    end
end

struct TableauLeaf
    leafnode::Ref{TableauNode}
    expansionnode::Ref{TableauNode}

    function TableauLeaf(leafnode::Ref{TableauNode}, expansionnode::Ref{TableauNode})
        return new(leafnode, expansionnode)
    end
end

struct HeapNode
    weight::Int
    leaf::TableauLeaf

    function HeapNode(weight::Int, leaf::TableauLeaf)
        return new(weight, leaf)
    end
end

function weight(heapnode::HeapNode)
    return heapnode.weight
end

struct WeightOrdering <: Base.Order.Ordering end

import Base.Order.lt
lt(o::WeightOrdering, a::HeapNode, b::HeapNode) = isless(weight(a), weight(b))

function leaf(heapnode::HeapNode)::TableauLeaf
    return heapnode.leaf
end

struct InformationHeap
    heap::BinaryHeap{HeapNode}
    informationtype::Function

    function InformationHeap(heap::BinaryHeap{HeapNode}, informationtype::Function)::InformationHeap
        return new(heap, informationtype)
    end

    function InformationHeap(informationtype::Function)
        return InformationHeap(BinaryHeap{HeapNode}(WeightOrdering()), informationtype)::InformationHeap
    end
end

function heap(informationheap::InformationHeap)::AbstractHeap{HeapNode}
    return informationheap.heap
end

function informationtype(informationheap::InformationHeap)::Function
    return informationheap.informationtype
end

function chooseleaf(heaps::Set{InformationHeap})::TableauLeaf
    candidates = Vector{TableauLeaf}()
    for informationheap ∈ heaps
        push!(candidates, leaf(first(heap(informationheap))))
    end
    candidatesdict = countmap(candidates)
    return collect(keys(candidatesdict))[argmax(collect(values(candidatesdict)))]
end

function sat(leavesset::Set{TableauLeaf}, heaps::Set{InformationHeap})
    leaf = chooseleaf(heaps)
    println(leaf)
end

function sat(φ::Formula, information::Function...)
    # Init
    leavesset = Set{TableauLeaf}()
    heaps = Set{InformationHeap}() # Heaps to be used for leaf selection based on meta-data information

    for informationtype ∈ information
        push!(heaps, InformationHeap(informationtype))
    end

    rootnode = TableauNode(φ)
    rootleaf = TableauLeaf(Ref(rootnode), Ref(rootnode))

    push!(leavesset, rootleaf)
    for informationheap ∈ heaps
        push!(heap(informationheap), HeapNode(informationtype(informationheap)(φ), rootleaf))
    end
    
    sat(leavesset, heaps)
end

end # module Reasoners
