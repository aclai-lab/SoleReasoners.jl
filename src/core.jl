############################################################################################
#### AbstractTableau #######################################################################
############################################################################################

"""
    abstract type AbstractTableau end

Abstract type for all tableaux structures.

An [analytic tableau](https://en.wikipedia.org/wiki/Method_of_analytic_tableaux) is a tree
structure computed for a logical formula having at each node a subformula of the original
formula to be proved or refuted. It is used in many automated reasoning tasks, such as
[automated theorem proving](https://en.wikipedia.org/wiki/Automated_theorem_proving) and the
[satifiability problem](https://en.wikipedia.org/wiki/Boolean_satisfiability_problem).

See also [`Tableau`](@ref), [`FuzzyTableau`](@ref).
"""
abstract type AbstractTableau end

############################################################################################
#### Tableau ###############################################################################
############################################################################################

"""
    mutable struct Tableau <: AbstractTableau
        const formula::Formula
        const father::Union{Tableau, Nothing}
        children::Set{Tableau}
        expanded::Bool
        closed::Bool
    end
    
A mutable structure representing a tableau as a tree structure, with each node containing
a subformula of the original formula, the father and children in the tree structure, a flag
saying if the node has already been expanded and a flag saying if the branch represented by
the node has been closed. Each path from a leaf to the root respresents a branch.

See also [`sat`](@ref), [`prove`](@ref).
"""
mutable struct Tableau <: AbstractTableau
    const formula::Formula
    const father::Union{Tableau, Nothing}
    children::Vector{Tableau}
    expanded::Bool
    closed::Bool

    function Tableau(formula::Formula)
        return new(formula, nothing, Vector{Tableau}(), false, false)
    end

    function Tableau(formula::Formula, father::Tableau)
        tableau = new(formula, father, Vector{Tableau}(), false, false)
        pushchild!(father, tableau)
        return tableau
    end
end

"""
    formula(tableau::Tableau) = tableau.formula

Return the formula of a tableau.
"""
formula(tableau::Tableau) = tableau.formula

"""
    father(tableau::Tableau)

Return the father of a tableau.
"""
function father(tableau::Tableau)
    return tableau.father
end

"""
    children(tableau::Tableau)

Return the children of a tableau.
"""
children(tableau::Tableau) = tableau.children

"""
    isexpanded(tableau::Tableau)

Return true if the tableau has been expanded, false otherwise.
"""
isexpanded(tableau::Tableau) = tableau.expanded

"""
    isclosed(tableau::Tableau)

Return true if the tableau has been closed, false otherwise.
"""
isclosed(tableau::Tableau) = tableau.closed

"""

"""
expand!(tableau::Tableau) = tableau.expanded = true
close!(tableau::Tableau) = tableau.closed = true

isroot(tableau::Tableau) = isnothing(father(tableau))

function findexpansionnode(tableau::Tableau)
    if isexpanded(tableau)
        return nothing
    elseif isroot(tableau) || isexpanded(father(tableau))
        return tableau
    else
        findexpansionnode(father(tableau))
    end
end

"""
    leaves(leavesset::Set{Tableau}, tableau::Tableau)

Getter for the leaves of a tableau.
"""
function leaves(leavesset::Set{Tableau}, tableau::Tableau)
    if isempty(children(tableau))
        push!(leavesset, tableau)
    else
        for child ∈ children(tableau)
            leaves(leavesset, child)
        end
    end
    return leavesset
end

"""
    leaves(tableau::Tableau)

Getter for the leaves of a tableau.
"""
function leaves(tableau::Tableau)
    leaves(Set{Tableau}(), tableau)
end

"""
    pushchild!(tableau::Tableau, newchild::Tableau...)

Push new child to a tableau.
"""
function pushchild!(tableau::Tableau, newchild::Tableau)
    push!(children(tableau), newchild)
end

"""
    isleaf(tableau::Tableau)

Return true if the tableau is still a leaf, false otherwise.
"""
isleaf(tableau::Tableau) = isempty(children(tableau)) ? true : false

############################################################################################
#### MetricHeapNode ########################################################################
############################################################################################

"""
    struct MetricHeapNode{T<:AbstractTableau}
        metricvalue::Int
        tableau::T
    end

The atomic element of a MetricHeap, it contains a tableau branch and a value for the metric
associated with the MetricHeap it is contained in.
"""
struct MetricHeapNode{T<:AbstractTableau}
    metricvalue::Int
    tableau::T

    function MetricHeapNode(metricvalue::Int, tableau::T) where {T<:AbstractTableau}
        return new{T}(metricvalue, tableau)
    end

    function MetricHeapNode(metric::Function, tableau::T) where {T<:AbstractTableau}
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
    lt(o::MetricHeapOrdering, a::MetricHeapNode, b::MetricHeapNode)

Definition of the lt function for the new ordering.
"""
function lt(o::MetricHeapOrdering, a::MetricHeapNode, b::MetricHeapNode)
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

    function MetricHeap(heap::BinaryHeap{MetricHeapNode}, metric::Function)
        return new(heap, metric)
    end

    function MetricHeap(metric::Function)
        heap = BinaryHeap{MetricHeapNode}(MetricHeapOrdering())
        return MetricHeap(heap, metric)
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
function push!(metricheap::MetricHeap,
               metricheapnode::MetricHeapNode)
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
isempty(metricheap::MetricHeap) = DataStructures.isempty(heap(metricheap))

############################################################################################
#### SAT ###################################################################################
############################################################################################

"""
    naivechooseleaf(metricheaps::Vector{MetricHeap})

Choose a leaf using the provided metric heaps.
At this moment, it simply returns the leaf which compares the most as head of the heaps.

To prevent starvation, use roundrobin instead.
"""
function naivechooseleaf(metricheaps::Vector{MetricHeap})
    candidates = Vector{AbstractTableau}()
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
    roundrobin(metricheaps::Vector{MetricHeap}, cycle::Int)

Choose a leaf using the provided metric heaps, alternating between them at each cycle.
"""
function roundrobin(metricheaps::Vector{MetricHeap}, cycle::Int)
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
    push!(metricheaps::Vector{MetricHeap}, tableau::T) where {T<:AbstractTableau}

Push leaf to each metric heap.
"""
function push!(metricheaps::Vector{MetricHeap}, tableau::T) where {T<:AbstractTableau}
    for metricheap ∈ metricheaps
        push!(metricheap, tableau)
    end
end

children(formula::Formula) = SoleLogics.children(formula)

function findsimilar(t::Tableau)
    x = formula(t)
    if x isa Atom
        while !isroot(t)
            t = father(t)
            if formula(t) == ¬x
                return true
            end
        end
    elseif token(x) isa NamedConnective{:¬}
        while !isroot(t)
            t = father(t)
            if formula(t) == first(children(x))
                return true
            end
        end
    else
        error("Something went wrong...")
    end
    return false
end

"""
    sat(metricheaps::Vector{MetricHeap}, chooseleaf::Function)

Given a formula, return true if an interpretation that satisfies the formula exists, false
otherwise.
"""
function sat(metricheaps::Vector{MetricHeap}, chooseleaf::Function)
    cycle = 0
    while true
        cycle%1e5==0 && getfreemem() < gettotmem()*2e-1 && error("Too much memory being used, exiting")
        leaf = chooseleaf(metricheaps, cycle)
        isnothing(leaf) && return false # all branches are closed
        en = findexpansionnode(leaf)
        isnothing(en) && return true    # found a satisfiable branch
        isclosed(en) && continue

        φ = formula(en)
        if φ isa Atom
            # Atom case
            if findsimilar(en)
                close!(en)
            else
                expand!(en)
                push!(metricheaps, leaf)
            end
        else
            tok = token(φ)
            if tok isa NamedConnective{:¬}
                # Negation case
                φi = first(children(φ))
                if φi isa Atom
                    # ¬φi where φi is an atom case
                    if findsimilar(en)
                        close!(en)
                    else
                        expand!(en)
                        push!(metricheaps, leaf)
                    end
                else
                    tok = token(φi)
                    if tok isa NamedConnective{:¬}
                        expand!(en)
                        for leaf ∈ leaves(en)
                            t = Tableau(first(children(φi)), leaf)
                            push!(metricheaps, t)
                        end
                    elseif tok isa NamedConnective{:∨}
                        expand!(en)
                        for l ∈ leaves(en)
                            (a, b) = children(φi)
                            ta = Tableau(¬a, l)
                            tb = Tableau(¬b, ta)
                            push!(metricheaps, tb)
                        end
                    elseif tok isa NamedConnective{:∧}
                        expand!(en)
                        for l ∈ leaves(en)
                            (a, b) = children(φi)
                            ta = Tableau(¬a, l)
                            tb = Tableau(¬b, l)
                            push!(metricheaps, ta)
                            push!(metricheaps, tb)
                        end
                    elseif tok isa NamedConnective{:→}
                        expand!(en)
                        (a, b) = children(φi)
                        for l ∈ leaves(en)
                            ta = Tableau(a, l)
                            tb = Tableau(¬b, ta)
                            push!(metricheaps, tb)
                        end
                    elseif tok isa BooleanTruth
                        if istop(tok)
                            close!(en)
                        elseif isbot(tok)
                            expand!(en)
                            push!(metricheaps, leaf)   # Push leaf back inside heap
                        end
                    else
                        error("Error: unrecognized token: ... ")
                    end
                end
            elseif tok isa NamedConnective{:∨}
                # Disjunction case
                expand!(en)
                for l ∈ leaves(en)
                    (a, b) = children(φ)
                    ta = Tableau(a, l)
                    tb = Tableau(b, l)
                    push!(metricheaps, ta)
                    push!(metricheaps, tb)
                end
            elseif tok isa NamedConnective{:∧}
                expand!(en)
                # Conjunction case
                for l ∈ leaves(en)
                    (a, b) = children(φ)
                    ta = Tableau(a, l)
                    tb = Tableau(b, ta)
                    push!(metricheaps, tb)
                end
            elseif tok isa NamedConnective{:→}
                expand!(en)
                # Implication case
                (a, b) = children(φ)
                for l ∈ leaves(en)
                    ta = Tableau(¬a, l)
                    tb = Tableau(b, l)
                    push!(metricheaps, ta)
                    push!(metricheaps, tb)
                end
            elseif tok isa BooleanTruth
                if istop(tok)
                    expand!(en)
                    push!(metricheaps, leaf)   # Push leaf back inside heap
                elseif isbot(tok)
                    close!(en)
                end
            else
                error("Error: unrecognized NamedConnective ")
            end
        end
        cycle += 1
    end
end

"""
    sat(formula::Formula, chooseleaf::Function, metrics::Function...)

Given a formula, return true if an interpretation that satisfies the formula exists, false
otherwise.
"""
function sat(formula::Formula, chooseleaf::Function, metrics::Function...)
    metricheaps = Vector{MetricHeap}()   # Heaps to be used for tableau selection
    for metric ∈ metrics
        push!(metricheaps, MetricHeap(metric))
    end
    root = Tableau(formula)
    for metricheap ∈ metricheaps
        push!(heap(metricheap), MetricHeapNode(metric(metricheap), root))
    end
    sat(metricheaps, chooseleaf)
end

"""
    sat(formula::Formula, chooseleaf::Function; rng = Random.GLOBAL_RNG)

Given a formula, return true if an interpretation that satisfies the formula exists, false
otherwise.
"""
function sat(formula::Formula, chooseleaf::Function; rng = Random.GLOBAL_RNG)
    randombranch(tableau::Tableau) = rand(rng, Int)
    sat(formula, chooseleaf, randombranch)
end

"""
    sat(formula::Formula; rng = Random.GLOBAL_RNG)

Given a formula, return true if an interpretation that satisfies the formula exists, false
otherwise.
"""
function sat(formula::Formula; rng = Random.GLOBAL_RNG)
    randombranch(tableau::Tableau) = rand(rng, Int)
    sat(formula, roundrobin, randombranch)
end
