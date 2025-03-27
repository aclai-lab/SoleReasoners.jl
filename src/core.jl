using SoleLogics: Formula

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
"""
abstract type AbstractTableau end

############################################################################################
#### Tableau ###############################################################################
############################################################################################

"""
    mutable struct Tableau <: AbstractTableau
        const formula::Formula
        const father::Union{Tableau, Nothing}
        children::Vector{Tableau}
        expanded::Bool
        closed::Bool
    end
    
A mutable structure representing a tableau as a tree structure, with each node containing
a subformula of the original formula, the father and children in the tree structure, a flag
saying if the node has already been expanded and a flag saying if the branch represented by
the node has been closed. Each path from a leaf to the root respresents a branch.
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
    father(tableau::T) where {T<:AbstractTableau}

Return the father of a tableau.
"""
function father(tableau::T) where {T<:AbstractTableau}
    return tableau.father
end

"""
    children(tableau::T) where {T<:AbstractTableau}

Return the children of a tableau.
"""
children(tableau::T) where {T<:AbstractTableau} = tableau.children

"""
    isexpanded(tableau::T) where {T<:AbstractTableau}

Return true if the tableau has been expanded, false otherwise.
"""
isexpanded(tableau::T) where {T<:AbstractTableau} = tableau.expanded

"""
    isclosed(tableau::T) where {T<:AbstractTableau}

Return true if the tableau has been closed, false otherwise.
"""
isclosed(tableau::T) where {T<:AbstractTableau} = tableau.closed

"""
    expand!(tableau::T) where {T<:AbstractTableau}

Set expanded flag to true.
"""
expand!(tableau::T) where {T<:AbstractTableau} = tableau.expanded = true

"""
    close!(tableau::T) where {T<:AbstractTableau}

Set closed flag to true (also for descendants).
"""
function close!(tableau::T) where {T<:AbstractTableau}
    tableau.closed = true
    while !isempty(tableau.children)
        c = pop!(tableau.children)
        close!(c)
    end
end

"""
    isroot(tableau::T) where {T<:AbstractTableau}

Return true if `tableau` is the root of the tableau.
"""
isroot(tableau::T) where {T<:AbstractTableau} = isnothing(father(tableau))

"""
    findexpansionnode(tableau::T) where {T<:AbstractTableau}

Return the expansion node related to the branch.
"""
function findexpansionnode(tableau::T) where {T<:AbstractTableau}
    if isroot(tableau) || isexpanded(father(tableau))
        return tableau
    else
        findexpansionnode(father(tableau))
    end
end

"""
    leaves(leavesset::Vector{T}, tableau::T) where {T<:AbstractTableau}

Getter for the leaves of a tableau.
"""
function leaves(leavesset::Vector{T}, tableau::T) where {T<:AbstractTableau}
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
    leaves(tableau::T) where {T<:AbstractTableau}

Getter for the leaves of a tableau.
"""
function leaves(tableau::T) where {T<:AbstractTableau}
    leaves(Vector{T}(), tableau)
end

"""
    pushchild!(tableau::T, newchild::T) where {T<:AbstractTableau}

Push new child to a tableau.
"""
function pushchild!(tableau::T, newchild::T) where {T<:AbstractTableau}
    push!(children(tableau), newchild)
end

"""
    isleaf(tableau::T) where {T<:AbstractTableau}

Return true if the tableau is still a leaf, false otherwise.
"""
isleaf(tableau::T) where {T<:AbstractTableau} = isempty(children(tableau)) ? true : false

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

    function MetricHeapNode(metric::F, tableau::T) where {F<:Function, T<:AbstractTableau}
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
mutable struct MetricHeap{F<:Function}
    const metric::F
    heap::BinaryHeap{MetricHeapNode}

    function MetricHeap(metric::F, heap::BinaryHeap{MetricHeapNode}) where {F<:Function}
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
isempty(metricheap::MetricHeap) = DataStructures.isempty(heap(metricheap))

function cleanheap!(metricheap::MetricHeap)
    elements = extract_all!(metricheap.heap)
    deleteat!(elements, findall(x->(isexpanded(x.tableau) && !isleaf(x.tableau)), elements))
    deleteat!(elements, findall(x->isclosed(x.tableau), elements))
    metricheap.heap = BinaryHeap{MetricHeapNode}(MetricHeapOrdering(), elements)
end

function cleanheaps!(metricheaps::Vector{MetricHeap})
    for mh in metricheaps
        cleanheap!(mh)
    end
end

############################################################################################
#### SAT ###################################################################################
############################################################################################

"""
    naivechoosenode(metricheaps::Vector{MetricHeap})

Choose a leaf using the provided metric heaps.
At this moment, it simply returns the leaf which compares the most as head of the heaps.

To prevent starvation, use roundrobin instead.
"""
function naivechoosenode(metricheaps::Vector{MetricHeap})
    candidates = Vector{AbstractTableau}()
    for metricheap ∈ metricheaps
        while !isempty(metricheap)
            head = tableau(first(heap(metricheap)))

            if isclosed(node)
                pop!(metricheap)
                continue
            elseif isexpanded(node)
                if isleaf(node)
                    return node # found a satisfiable branch
                else
                    pop!(metricheap)
                    continue
                end
            else
                push!(candidates, head)
                break
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
    naivechoosenode(metricheaps::Vector{MetricHeap}, _::Int)

Choose a leaf using the provided metric heaps.
At this moment, it simply returns the leaf which compares the most as head of the heaps.

To prevent starvation, use roundrobin instead.
"""
function naivechoosenode(metricheaps::Vector{MetricHeap}, _::Int)
    naivechoosenode(metricheaps)
end

"""
    roundrobin(metricheaps::Vector{MetricHeap}, cycle::Int)

Choose a node using the provided metric heaps, alternating between them at each cycle.

The result can either be nothing, in case all heaps are empty and therefore the tableau is
closed, or a node; an expanded node can only be returned if it is a leaf and in that case
it represents a satisfiable branch for the tableau (i.e., a fully expanded open branch
without contraddictions).
"""
function roundrobin(metricheaps::Vector{MetricHeap}, cycle::Int)
    counter = 0
    node = nothing
    while counter != length(metricheaps)
        metricheap = metricheaps[((cycle + counter) % length(metricheaps)) + 1]
        while !isempty(metricheap)
            node = pop!(metricheap)
            if isclosed(node)
                continue
            elseif isexpanded(node)
                if isleaf(node)
                    return node # found a satisfiable branch
                else
                    continue
                end
            else
                return node
            end
        end
        counter += 1    # try next heap
    end
    return nothing  # all heaps are empty, therefore the tableau is closed
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

function sat(metricheaps::Vector{MetricHeap}, choosenode::F) where {F<:Function}
    cycle = 1
    while true

        if cycle%1e3==0
            cleanheaps!(metricheaps)
        end

        # if using too much memory, try to free memory calling full GC sweep
        if cycle%10==0 && getfreemem() < gettotmem()*5e-2
            verbose && println("Calling Garbage Collector")
            GC.gc()
        end
        # if using too much memory, kill execution to avoid crashes
        if cycle%10==0 && getfreemem() < gettotmem()*5e-2
            error("Too much memory being used, exiting")
        end
        
        leaf = choosenode(metricheaps, cycle)
        isnothing(leaf) && return false # all branches are closed
        isexpanded(leaf) && return true # found a satisfiable branch
        en = findexpansionnode(leaf)
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
    sat(formula::Formula, choosenode::Function, metrics::Function...)

Given a formula, return true if an interpretation that satisfies the formula exists, false
otherwise.

*choosenode* should be a function taking a vector of metricheaps as an argument (and
eventually a counter) and giving a tableau (or nothing) as output that is used to extract a
node representing a branch to be expanded. If nothing, all branches are closed.

*metrics* should be functions taking a tableau as an argument and giving an integer as
output that are used to model the order in which tableau branches are expanded. For example,
one could declare the following metric functions:

    mf1(t::Tableau) = noperators(t.formula)
    mf2(t::Tableau) = height(t.formula)

The first metric will generate a metricheap proposing to expand first branches comprising
the node containing the formula with the less number of operators, the second metric will
generate a metricheap proposing to expand first branches comprising the node containing the
formula of less height.

*choosenode* will then be used to choose which policy to follow (e.g., choosing the node
voted by most heaps, or alternating between each heap at each cycle).
"""
function sat(formula::Formula, choosenode::F, metrics::Function...) where {F<:Function}
    metricheaps = Vector{MetricHeap}()   # Heaps to be used for tableau selection
    for metric ∈ metrics
        push!(metricheaps, MetricHeap(metric))
    end
    root = Tableau(formula)
    for metricheap ∈ metricheaps
        push!(heap(metricheap), MetricHeapNode(metric(metricheap), root))
    end
    return sat(metricheaps, choosenode)
end

"""
    sat(formula::Formula, metric::F; rng = Random.GLOBAL_RNG) where {F<:Function}

Given a formula and an extraction policy metric, return true if an interpretation that
satisfies the formula exists, false otherwise.

*metric* should be a function taking a tableau as an argument and giving an integer as
output that is used to model the order in which tableau branches are expanded. For example,
one could declare the following metric function:

    mf(t::Tableau) = noperators(t.formula)

This way, the tableau will be expanded giving precedence to branches comprising nodes
containing formulae with the smallest number operators.
"""
function sat(formula::Formula, metric::F; kwargs...) where {F<:Function}
    return sat(formula, roundrobin, metric)
end

"""
    sat(formula::Formula; rng = Random.GLOBAL_RNG)

Given a formula, return true if an interpretation that satisfies the formula exists, false
otherwise.
"""
function sat(formula::Formula; rng = Random.GLOBAL_RNG, kwargs...)
    randombranch(_::Tableau) = rand(rng, Int)
    return sat(formula, randombranch)
end

"""
    sat(formula::Formula, choosenode::Function, metrics::Function...)

Given a formula, return true if it is valid, i.e., there is not an interpretation that does
not satisfy the formula, false otherwise.

*choosenode* should be a function taking a vector of metricheaps as an argument (and
eventually a counter) and giving a tableau (or nothing) as output that is used to extract a
node representing a branch to be expanded. If nothing, all branches are closed.

*metrics* should be functions taking a tableau as an argument and giving an integer as
output that are used to model the order in which tableau branches are expanded. For example,
one could declare the following metric functions:

    mf1(t::Tableau) = noperators(t.formula)
    mf2(t::Tableau) = height(t.formula)

The first metric will generate a metricheap proposing to expand first branches comprising
the node containing the formula with the less number of operators, the second metric will
generate a metricheap proposing to expand first branches comprising the node containing the
formula of less height.

*choosenode* will then be used to choose which policy to follow (e.g., choosing the node
voted by most heaps, or alternating between each heap at each cycle).
"""
function prove(formula::Formula, choosenode::F, metrics::Function...) where {F<:Function}
    metricheaps = Vector{MetricHeap}()   # Heaps to be used for tableau selection
    for metric ∈ metrics
        push!(metricheaps, MetricHeap(metric))
    end
    root = Tableau(¬(formula))
    for metricheap ∈ metricheaps
        push!(heap(metricheap), MetricHeapNode(metric(metricheap), root))
    end
    return !sat(metricheaps, choosenode)
end

"""
    prove(formula::Formula, metric::F; kwargs...) where {F<:Function}

Given a formula, return true if it is valid, i.e., there is not an interpretation that does
not satisfy the formula, false otherwise.

*metric* should be a function taking a tableau as an argument and giving an integer as
output that is used to model the order in which tableau branches are expanded. For example,
one could declare the following metric function:

    mf(t::Tableau) = noperators(t.formula)
    
This way, the tableau will be expanded giving precedence to branches comprising nodes
containing formulae with the smallest number operators.
"""
function prove(formula::Formula, metric::F; kwargs...) where {F<:Function}
    randombranch(_::Tableau) = rand(rng, Int)
    return prove(formula, roundrobin, metric)
end

"""
    prove(formula::Formula; rng = Random.GLOBAL_RNG)

Given a formula, return true if it is valid, i.e., there is not an interpretation that does
not satisfy the formula, false otherwise.
"""
function prove(formula::Formula; rng = Random.GLOBAL_RNG, kwargs...)
    randombranch(_::Tableau) = rand(rng, Int)
    return prove(formula, randombranch)
end
