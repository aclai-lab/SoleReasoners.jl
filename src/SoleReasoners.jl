module SoleReasoners

export Tableau, φ, literals, naivechooseleaf, roundrobin, sat, dimacstosole

using DataStructures
using StatsBase
using Random
using Reexport

@reexport using SoleLogics

import Base: isempty, push!, Base.pop!, Order.lt

############################################################################################
#### Tableau ###############################################################################
############################################################################################

"""
    struct Tableau
        φ::Formula
        father::Base.RefValue{Set{Tableau}}
        children::Base.RefValue{Set{Tableau}}
        literals::Base.RefValue{Set{Formula}}
    end
A recursive structure resembling a tree which contains a formula φ (which structure is
defined in the SoleLogics package) and references to the father, the set of children and
the set of literals (atoms and negation of atoms) found in the same branch.

A tableau is a dynamic structure used to solve the satisfiability problem following the
analytic tableau approach. At a specific instant in time, the root represents a possible
expansion node of the tableau, while each path from a root to one of its leaves represents
a branch, with literals in the leaves containing the literals (atoms and negation of atoms)
encountered it the expanded nodes for that branch.
    
This allows to delegate to the Julia garbage collector the deallocation of expanded nodes,
while simplifying root (expansion node) search and branch management.

Note that, while at initialization only there is only one root, the structure later on
can be divided in many tree-like structures, with each root representing an expansion node
and each set of leaves representing the leaves (or branches) associated with that expansion
node.
"""
struct Tableau
    φ::Formula
    father::Base.RefValue{Set{Tableau}} # Note that this set contains at most one element
    children::Base.RefValue{Set{Tableau}}
    literals::Base.RefValue{Set{Formula}}

    function Tableau(φ::Formula, father::Base.RefValue{Set{Tableau}},
                     children::Base.RefValue{Set{Tableau}},
                     literals::Base.RefValue{Set{Formula}})::Tableau
        return new(φ, father, children, literals)
    end

    function Tableau(φ::Formula)::Tableau
        return Tableau(φ, Ref(Set{Tableau}()), Ref(Set{Tableau}()), Ref(Set{Formula}()))
    end

    function Tableau(φ::Formula, father::Base.RefValue{Set{Tableau}})::Tableau
        return Tableau(φ, father, Ref(Set{Tableau}()), Ref(Set{Formula}()))
    end

    function Tableau(φ::Formula, father::Tableau)::Tableau
        tableau = Tableau(φ, Ref(Set{Tableau}([father])))
        pushchildren!(father, tableau)
        for atom in literals(father)
            pushliterals!(tableau, atom)
        end
        return tableau
    end
end

"""
    φ(tableau::Tableau)::Formula = tableau.φ

Getter for the formula of a tableau.
"""
φ(tableau::Tableau)::Formula = tableau.φ

"""
    fatherset(tableau::Tableau)::Set{Tableau} = tableau.father[]

Getter for the set containing the father of a tableau.
"""
fatherset(tableau::Tableau)::Set{Tableau} = tableau.father[]

"""
    father(tableau::Tableau)::Union{Tableau, Nothing}

Getter for the father of a tableau.
"""
function father(tableau::Tableau)::Union{Tableau, Nothing}
    return isempty(fatherset(tableau)) ? nothing : first(fatherset(tableau))
end

"""
    childrenset(tableau::Tableau)::Set{Tableau}

Getter for the set containing the children of a tableau.
"""
childrenset(tableau::Tableau)::Set{Tableau} = tableau.children[]

"""
    literals(tableau::Tableau)::Set{Formula}

Getter for the set containing the literals of a tableau.
"""
literals(tableau::Tableau)::Set{Formula} = tableau.literals[]

"""
    leaves(leavesset::Set{Tableau}, tableau::Tableau)::Set{Tableau}

Getter for the leaves of a tableau.
"""
function leaves(leavesset::Set{Tableau}, tableau::Tableau)::Set{Tableau}
    children = childrenset(tableau)
    if isempty(children)
        push!(leavesset, tableau)
    else
        for child ∈ children
            leaves(leavesset, child)
        end
    end
    return leavesset
end

"""
    leaves(tableau::Tableau)::Set{Tableau}

Getter for the leaves of a tableau.
"""
function leaves(tableau::Tableau)::Set{Tableau}
    leaves(Set{Tableau}(), tableau)
end

"""
    pushfather!(tableau::Tableau, newfather::Tableau)::Set{Tableau}

Push new father to a tableau.
"""
function pushfather!(tableau::Tableau, newfather::Tableau)::Set{Tableau}
    push!(fatherset(tableau), newfather)
end

"""
    popfather!(tableau::Tableau)::Tableau

Pop father of a tableau (the tableau becomes a root).
"""
popfather!(tableau::Tableau)::Tableau = pop!(fatherset(tableau))

"""
    pushchildren!(tableau::Tableau, children::Tableau...)::Set{Tableau}

Push new children to a tableau.
"""
function pushchildren!(tableau::Tableau, children::Tableau...)::Set{Tableau}
    push!(childrenset(tableau), children...)
end

"""
    pushliterals!(tableau::Tableau, newliterals::Formula...)::Set{Formula}

Push new literals to a tableau.
"""
function pushliterals!(tableau::Tableau, newliterals::Formula...)::Set{Formula}
    push!(literals(tableau), newliterals...)
end

"""
    findroot(tableau::Tableau)::Tableau

Find root starting from the leaf (i.e., the expansion node relative to that leaf).
"""
function findroot(tableau::Tableau)::Tableau
    isnothing(father(tableau)) ? tableau : findroot(father(tableau))
end

"""
    isleaf(tableau::Tableau)::Bool

Return true if the tableau is still a leaf, false otherwise.
"""
isleaf(tableau::Tableau)::Bool = isempty(childrenset(tableau)) ? true : false

############################################################################################
#### MetricHeapNode ########################################################################
############################################################################################

"""
    struct MetricHeapNode
        metricvalue::Int
        tableau::Tableau
    end

The atomic element of a MetricHeap, it contains a tableau branch and a value for the metric
associated with the MetricHeap it is contained in.
"""
struct MetricHeapNode
    metricvalue::Int
    tableau::Tableau

    function MetricHeapNode(metricvalue::Int, tableau::Tableau)::MetricHeapNode
        return new(metricvalue, tableau)::MetricHeapNode
    end

    function MetricHeapNode(metric::Function, tableau::Tableau)::MetricHeapNode
        MetricHeapNode(metric(tableau), tableau)::MetricHeapNode
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

############################################################################################
#### MetricHeapOrdering ####################################################################
############################################################################################

"""
    struct MetricHeapOrdering <: Base.Order.Ordering end

Definition of a new ordering for the heaps treating them as min heaps ordered on the
metric value.
"""
struct MetricHeapOrdering <: Base.Order.Ordering end

"""
    lt(o::MetricHeapOrdering, a::MetricHeapNode, b::MetricHeapNode)::Bool

Definition of the lt function for the new ordering.
"""
function lt(o::MetricHeapOrdering, a::MetricHeapNode, b::MetricHeapNode)::Bool
    isless(metricvalue(a), metricvalue(b))
end

############################################################################################
#### MetricHeap ############################################################################
############################################################################################

"""
    struct MetricHeap
        heap::BinaryHeap{MetricHeapNode}
        metric::Function
    end

A MetricHeap is basically a heap parametrized over a metric, i.e., a function which extracts
some information about a tableau branch, therefore containing in each node a tableau branch
and the relative value for the metric, and which is ordered as a min heap over this
metric value.
"""
struct MetricHeap
    heap::BinaryHeap{MetricHeapNode}
    metric::Function

    function MetricHeap(heap::BinaryHeap{MetricHeapNode}, metric::Function)::MetricHeap
        return new(heap, metric)
    end

    function MetricHeap(metric::Function)::MetricHeap
        heap = BinaryHeap{MetricHeapNode}(MetricHeapOrdering())
        return MetricHeap(heap, metric)::MetricHeap
    end
end

"""
    heap(metricheap::MetricHeap)::BinaryHeap{MetricHeapNode}

Getter for the binary heap of a MetricHeap.
"""
heap(metricheap::MetricHeap)::BinaryHeap{MetricHeapNode} = metricheap.heap

"""
    metric(metricheap::MetricHeap)::Function

Getter for the metric function of a MetricHeap.
"""
metric(metricheap::MetricHeap)::Function = metricheap.metric

"""
    push!(metricheap::MetricHeap, metricheapnode::MetricHeapNode)::BinaryHeap{MetricHeapNode}
    
Push new metricheapnode to a MetricHeap.
"""
function push!(metricheap::MetricHeap,
               metricheapnode::MetricHeapNode)::BinaryHeap{MetricHeapNode}
    push!(heap(metricheap), metricheapnode)
end

"""
    push!(metricheap::MetricHeap, tableau::Tableau)::BinaryHeap{MetricHeapNode}

Push new tableau to a MetricHeap.
"""
function push!(metricheap::MetricHeap, tableau::Tableau)::BinaryHeap{MetricHeapNode}
    push!(metricheap, MetricHeapNode(metric(metricheap), tableau))
end

"""
    pop!(metricheap::MetricHeap)::Tableau

Pop head of a MetricHeap and return the tableau associated with it.
"""
pop!(metricheap::MetricHeap)::Tableau = tableau(pop!(heap(metricheap)))

"""
    isempty(metricheap::MetricHeap)::Bool

Returns true if the MetricHeap is empty, false otherwise.
"""
isempty(metricheap::MetricHeap)::Bool = DataStructures.isempty(heap(metricheap))

############################################################################################
#### SAT ###################################################################################
############################################################################################

"""
    naivechooseleaf(metricheaps::Vector{MetricHeap})::Union{Tableau, Nothing}

Choose a leaf using the provided metric heaps.
At this moment, it simply returns the leaf which compares the most as head of the heaps.

To prevent starvation, use roundrobin instead.
"""
function naivechooseleaf(metricheaps::Vector{MetricHeap})::Union{Tableau, Nothing}
    candidates = Vector{Tableau}()
    for metricheap ∈ metricheaps
        while !isempty(metricheap)
            head = tableau(first(heap(metricheap)))
            if isleaf(head)
                push!(candidates, head)
                break
            else
                pop!(metricheap)
            end
        end
    end
    candidatesdict = countmap(candidates)
    if isempty(candidatesdict)
        return nothing
    else
        return collect(keys(candidatesdict))[argmax(collect(values(candidatesdict)))]
    end
end

"""
    naivechooseleaf(metricheaps::Vector{MetricHeap}, _::Int)

Choose a leaf using the provided metric heaps.
At this moment, it simply returns the leaf which compares the most as head of the heaps.

To prevent starvation, use roundrobin instead.
"""
function naivechooseleaf(metricheaps::Vector{MetricHeap}, _::Int)
    naivechooseleaf(metricheaps)
end

"""
    roundrobin(metricheaps::Vector{MetricHeap}, cycle::Int)::Union{Tableau, Nothing}

Choose a leaf using the provided metric heaps, alternating between them at each cycle.
"""
function roundrobin(metricheaps::Vector{MetricHeap}, cycle::Int)::Union{Tableau, Nothing}
    counter = 0
    leaf = nothing
    while counter != length(metricheaps)
        metricheap = metricheaps[((cycle + counter) % length(metricheaps)) + 1]
        if !isempty(metricheap)
            leaf = pop!(metricheap)
            while (!isleaf(leaf) && !isempty(metricheap))
                leaf = pop!(metricheap)
            end
            if isleaf(leaf)
                break
            else
                counter +=1
            end
        else
            counter += 1
        end
    end
    if counter == length(metricheaps)
        return nothing
    else
        return leaf    
    end
end

"""
    push!(metricheaps::Vector{MetricHeap}, tableau::Tableau)::Nothing

Push leaf to each metric heap.
"""
function push!(metricheaps::Vector{MetricHeap}, tableau::Tableau)::Nothing
    for metricheap ∈ metricheaps
        push!(metricheap, tableau)
    end
end

"""
    sat(metricheaps::Vector{MetricHeap}, chooseleaf::Function)::Bool

Given a formula, return true if an interpretation that satisfies the formula exists, false
otherwise.
"""
function sat(metricheaps::Vector{MetricHeap}, chooseleaf::Function)::Bool
    cycle = 0
    while true
        leaf = chooseleaf(metricheaps, cycle)
        if isnothing(leaf)
            return false
        else
            root = findroot(leaf)
            φroot = φ(root)
            if φroot isa Atom
                # Atom case
                if leaf === root
                    if ¬φroot ∉ literals(leaf)
                        return true
                    else
                        # Create fake child and don't push it to heaps
                        pushfather!(leaf, leaf)
                        pushchildren!(leaf, leaf) # Use the node itself to not waste space
                    end
                else
                    push!(metricheaps, leaf)   # Push leaf back inside heaps
                    for l ∈ leaves(root)
                        if ¬φroot ∉ literals(l)
                            pushliterals!(l, φroot)
                        else
                            # Create fake child and don't push it to heaps
                            pushfather!(l, l)
                            pushchildren!(l, l) # Use the node itself to not waste space
                        end
                    end
                end
            else
                tok = token(φroot)
                if tok isa NamedConnective{:¬}
                    # Negation case
                    φi = children(φroot)[1]
                    if φi isa Atom
                        # ¬φi where φi is an atom case
                        if leaf === root
                            if φi ∉ literals(leaf)
                                return true
                            else
                                # Create fake child and don't push it to heap
                                pushfather!(leaf, leaf)
                                pushchildren!(leaf, leaf) # Use the node itself to not waste space
                            end
                        else
                            push!(metricheaps, leaf)   # Push leaf back inside heap
                            for l ∈ leaves(root)
                                if φi ∉ literals(l)
                                    pushliterals!(l, φroot)
                                else
                                    # Create fake child and don't push it to heap
                                    pushfather!(l, l)
                                    pushchildren!(l, l) # Use the node itself to not waste space
                                end
                            end
                        end
                    else
                        tok = token(φi)
                        if tok isa NamedConnective{:¬}
                            for leaf ∈ leaves(root)
                                t = Tableau(children(φi)[1], leaf)
                                push!(metricheaps, t)
                            end
                        elseif tok isa NamedConnective{:∨}
                            for l ∈ leaves(root)
                                t = l
                                for φj ∈ children(φi)
                                    t = Tableau(¬φj, t)
                                end
                                push!(metricheaps, t)
                            end
                        elseif tok isa NamedConnective{:∧}
                            for leaf ∈ leaves(root)
                                for φj ∈ children(φi)
                                    t = Tableau(¬φj, leaf)
                                    push!(metricheaps, t)
                                end
                            end
                        elseif tok isa NamedConnective{:→}
                            φ1, φ2 = children(φi)
                            φis = (φ1, ¬φ2)
                            for l ∈ leaves(root)
                                t = l
                                for φi ∈ children(φis)
                                    t = Tableau(φi, t)
                                end
                                push!(metricheaps, t)
                            end
                        elseif tok isa BooleanTruth
                            if leaf === root
                                return true
                            else
                                push!(metricheaps, leaf)   # Push leaf back inside heap
                            end
                        else
                            error("Error: unrecognized token: ... ")
                        end
                    end
                elseif tok isa NamedConnective{:∨}
                    # Disjunction case
                    for l ∈ leaves(root)
                        for φi ∈ children(φroot)
                            t = Tableau(φi, l)
                            push!(metricheaps, t)
                        end
                    end
                elseif tok isa NamedConnective{:∧}
                    # Conjunction case
                    for l ∈ leaves(root)
                        t = l
                        for φi ∈ children(φroot)
                            t = Tableau(φi, t)
                        end
                        push!(metricheaps, t)
                    end
                elseif tok isa NamedConnective{:→}
                    # Implication case
                    φ1, φ2 = children(φroot)
                    φis = (¬φ1, φ2)
                    for leaf ∈ leaves(root)
                        for φi ∈ φis
                            t = Tableau(φi, leaf)
                            push!(metricheaps, t)
                        end
                    end
                elseif tok isa BooleanTruth
                    if leaf === root
                        return true
                    else
                        push!(metricheaps, leaf)   # Push leaf back inside heap
                    end
                else
                    error("Error: unrecognized NamedConnective ")
                end
            end
            for child ∈ childrenset(root)
                popfather!(child)
            end
        end
        cycle += 1
    end
end

"""
    sat(φ::Formula, chooseleaf::Function, metrics::Function...)::Bool

Given a formula, return true if an interpretation that satisfies the formula exists, false
otherwise.
"""
function sat(φ::Formula, chooseleaf::Function, metrics::Function...)::Bool
    metricheaps = Vector{MetricHeap}()   # Heaps to be used for tableau selection
    for metric ∈ metrics
        push!(metricheaps, MetricHeap(metric))
    end
    root = Tableau(φ)
    for metricheap ∈ metricheaps
        push!(heap(metricheap), MetricHeapNode(metric(metricheap), root))
    end
    sat(metricheaps, chooseleaf)
end

"""
    sat(φ::Formula, chooseleaf::Function; rng = Random.GLOBAL_RNG)::Bool

Given a formula, return true if an interpretation that satisfies the formula exists, false
otherwise.
"""
function sat(φ::Formula, chooseleaf::Function; rng = Random.GLOBAL_RNG)::Bool
    randombranch(tableau::Tableau) = rand(rng, Int)
    sat(φ, chooseleaf, randombranch)
end

"""
    sat(φ::Formula; rng = Random.GLOBAL_RNG)::Bool

Given a formula, return true if an interpretation that satisfies the formula exists, false
otherwise.
"""
function sat(φ::Formula; rng = Random.GLOBAL_RNG)::Bool
    randombranch(tableau::Tableau) = rand(rng, Int)
    sat(φ, roundrobin, randombranch)
end

############################################################################################
#### Utils #################################################################################
############################################################################################

"""
    dimacstosole(dimacscnf::String)::Formula

Simple parsing from DIMACS CNF format to a SoleLogics Formula.

`dimacscnf` is the path of the file containing the formula in DIMACS CNF format.
TODO: cnftodimacs
"""
function dimacstosole(dimacscnf::String)::Formula
    disjunctions = Set{Formula}()
    for line in readlines(dimacscnf)
        if !startswith(line, "c") && !startswith(line, "p") && !startswith(line, "%") && !startswith(line, "0") && line != ""
            words = split(line)
            literals = Set{Formula}()
            for word ∈ words
                if word != "0"
                    if startswith(word, "-")
                        literal = ¬Atom(abs(parse(Int, word)))
                    else
                        literal = Atom(abs(parse(Int, word)))
                    end
                    push!(literals, literal)
                end
            end
            push!(disjunctions, ∨(literals...))
        end
    end
    return ∧(disjunctions...)
end

end # module SoleReasoners
