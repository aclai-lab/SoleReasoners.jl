module Reasoners

export sat

using SoleLogics
using DataStructures
using StatsBase

############################################################################################
#### TableauNode ###########################################################################
############################################################################################

"""
    struct TableauNode
        φ::Formula
        children::Base.RefValue{Set{TableauNode}}
    end

The atomic structure of a tableu, it contains a formula φ (which structure is defined in
the SoleLogics package) and a reference to a set of children tableau nodes.
"""
struct TableauNode
    φ::Formula
    children::Base.RefValue{Set{TableauNode}}

    function TableauNode(φ::Formula, children::Base.RefValue{Set{TableauNode}})
        return new(φ, children)
    end

    function TableauNode(φ::Formula, children::Set{TableauNode}) 
        return TableauNode(φ, Ref(children))
    end

    function TableauNode(φ::Formula)
        return TableauNode(φ, Set{TableauNode}())
    end
end

"""
Getter for the formula of a tableau node
"""
φ(tableaunode::TableauNode) = tableaunode.φ

"""
Getter for the children of a tableau node
"""
children(tableaunode::TableauNode) = tableaunode.children[]

"""
Add one or more children to a tableau node
"""
pushchildren!(tableaunode::TableauNode, children::TableauNode...) = push!(Reasoners.children(tableaunode), children...)

"""
Evaluate the height of the tableau node
"""
height(tableaunode::TableauNode) = length(children(tableaunode)) == 0 ? 0 : 1 + maximum(height(c) for c in children(tableaunode))

############################################################################################
#### TableauBranch #########################################################################
############################################################################################

"""
    struct TableauBranch
        leafnode::TableauNode
        expansionnode::TableauNode
    end

A branch of the tableau is characterized by leaf node and a respective expansion node
"""
struct TableauBranch
    leafnode::TableauNode
    expansionnode::TableauNode

    function TableauBranch(leafnode::TableauNode, expansionnode::TableauNode)
        return new(leafnode, expansionnode)
    end
end

"""
Getter for the leaf node of a tableau branch
"""
leafnode(tableaubranch::TableauBranch) = tableaubranch.leafnode


"""
Getter for the expansion node of a tableau branch
"""
expansionnode(tableaubranch::TableauBranch) = tableaubranch.expansionnode

struct HeapNode
    weight::Int
    tableaubranch::TableauBranch

    function HeapNode(weight::Int, tableaubranch::TableauBranch)
        return new(weight, tableaubranch)
    end
end

function weight(heapnode::HeapNode)
    return heapnode.weight
end

struct WeightOrdering <: Base.Order.Ordering end

import Base.Order.lt
lt(o::WeightOrdering, a::HeapNode, b::HeapNode) = isless(weight(a), weight(b))

function tableaubranch(heapnode::HeapNode)::TableauBranch
    return heapnode.tableaubranch
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

function chooseleaf(heaps::Set{InformationHeap})::TableauBranch
    candidates = Vector{TableauBranch}()
    for informationheap ∈ heaps
        push!(candidates, tableaubranch(first(heap(informationheap))))
    end
    candidatesdict = countmap(candidates)
    return collect(keys(candidatesdict))[argmax(collect(values(candidatesdict)))]
end

function sat(leavesset::Set{TableauBranch}, heaps::Set{InformationHeap})
    tableaubranch = chooseleaf(heaps)
    println(tableaubranch)
end

function sat(φ::Formula, information::Function...)
    # Init
    leavesset = Set{TableauBranch}()
    heaps = Set{InformationHeap}() # Heaps to be used for tableaubranch selection based on meta-data information

    for informationtype ∈ information
        push!(heaps, InformationHeap(informationtype))
    end

    rootnode = TableauNode(φ)
    rootleaf = TableauBranch(Ref(rootnode), Ref(rootnode))

    push!(leavesset, rootleaf)
    for informationheap ∈ heaps
        push!(heap(informationheap), HeapNode(informationtype(informationheap)(φ), rootleaf))
    end
    
    sat(leavesset, heaps)
end

end # module Reasoners
