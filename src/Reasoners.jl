module Reasoners

export sat

using SoleLogics
using DataStructures
using StatsBase

import Base.Order.lt

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
Getter for the formula of a tableau node.
"""
φ(tableaunode::TableauNode) = tableaunode.φ

"""
Getter for the children of a tableau node.
"""
children(tableaunode::TableauNode) = tableaunode.children[]

"""
Add one or more children to a tableau node.
"""
function pushchildren!(tableaunode::TableauNode, children::TableauNode...)
    push!(Reasoners.children(tableaunode), children...)
end

"""
Evaluate the height of the tableau node.
"""
function height(tableaunode::TableauNode)
    length(children(tableaunode)) == 0 ? 0 : 1 + maximum(height(c) for c in children(tableaunode))
end

############################################################################################
#### TableauBranch #########################################################################
############################################################################################

"""
    struct TableauBranch
        leafnode::TableauNode
        expansionnode::TableauNode
    end

A branch of the tableau is characterized by leaf node and a respective expansion node.
"""
struct TableauBranch
    leafnode::TableauNode
    expansionnode::TableauNode

    function TableauBranch(leafnode::TableauNode, expansionnode::TableauNode)
        return new(leafnode, expansionnode)
    end
end

"""
Getter for the leaf node of a tableau branch.
"""
leafnode(tableaubranch::TableauBranch) = tableaubranch.leafnode

"""
Getter for the expansion node of a tableau branch.
"""
expansionnode(tableaubranch::TableauBranch) = tableaubranch.expansionnode

############################################################################################
#### HeapNode ##############################################################################
############################################################################################

"""
    struct HeapNode
        value::Int
        tableaubranch::TableauBranch
    end

The atomic element of an heap, it contains a tableau branch and a value for it associated to
a specific kind of information, parameter of the respective heap.
"""
struct HeapNode
    informationvalue::Int
    tableaubranch::TableauBranch

    function HeapNode(informationvalue::Int, tableaubranch::TableauBranch)
        return new(informationvalue, tableaubranch)
    end
end

"""
Getter for the information value of a heap node.
"""
informationvalue(heapnode::HeapNode) = heapnode.informationvalue


"""
Getter for the tableau branch of a heap node.
"""
tableaubranch(heapnode::HeapNode) = heapnode.tableaubranch

############################################################################################
#### HeapOrdering ##########################################################################
############################################################################################

"""
Definition of a new ordering for the heaps treating them as min heaps ordered on the
information value.
"""
struct HeapOrdering <: Base.Order.Ordering end

"""
Definition of the lt function for the new ordering.
"""
function lt(o::HeapOrdering, a::HeapNode, b::HeapNode)
    isless(informationvalue(a), informationvalue(b))
end

############################################################################################
#### InformationHeap #######################################################################
############################################################################################

"""
    struct InformationHeap
        heap::BinaryHeap{HeapNode}
        informationtype::Function
    end

An information heap is basically a heap parametrized over an informationtype, i.e., a
function which extract some information about a tableau branch, therefore containing in each
node a tabluea branch and the relative information value, and which is ordered as a min heap
over this information value.
"""
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

"""
Getter for the heap of an information heap.
"""
heap(informationheap::InformationHeap)::AbstractHeap{HeapNode} = informationheap.heap

"""
Getter for the information type of an information heap.
"""
informationtype(informationheap::InformationHeap)::Function = informationheap.informationtype

############################################################################################
#### SAT ###################################################################################
############################################################################################

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
