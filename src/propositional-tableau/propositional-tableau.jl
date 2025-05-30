using SoleLogics: Formula, children as subformulas, ¬, ∨, ∧, →
using Random

################################################################################
#### Tableau ###################################################################
################################################################################

"""
    mutable struct Tableau <: AbstractTableau
        const formula::Formula
        const father::Union{Tableau, Nothing}
        children::Vector{Tableau}
        expanded::Bool
        closed::Bool
    end
    
A mutable structure representing a tableau as a tree structure, with each node
containing a subformula of the original formula, the father and children in the
tree structure, a flag saying if the node has already been expanded and a flag
saying if the branch represented by the node has been closed. Each path from a
leaf to the root respresents a branch.
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

################################################################################
#### SAT #######################################################################
################################################################################

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
            if formula(t) == first(subformulas(x))
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
        expanded(leaf) && return true # found a satisfiable branch
        en = findexpansionnode(leaf)
        closed(en) && continue

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
                φi = first(subformulas(φ))
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
                        for leaf ∈ findleaves(en)
                            t = Tableau(first(subformulas(φi)), leaf)
                            push!(metricheaps, t)
                        end
                    elseif tok isa NamedConnective{:∨}
                        expand!(en)
                        for l ∈ findleaves(en)
                            (a, b) = subformulas(φi)
                            ta = Tableau(¬a, l)
                            tb = Tableau(¬b, ta)
                            push!(metricheaps, tb)
                        end
                    elseif tok isa NamedConnective{:∧}
                        expand!(en)
                        for l ∈ findleaves(en)
                            (a, b) = subformulas(φi)
                            ta = Tableau(¬a, l)
                            tb = Tableau(¬b, l)
                            push!(metricheaps, ta)
                            push!(metricheaps, tb)
                        end
                    elseif tok isa NamedConnective{:→}
                        expand!(en)
                        (a, b) = subformulas(φi)
                        for l ∈ findleaves(en)
                            ta = Tableau(a, l)
                            tb = Tableau(¬b, ta)
                            push!(metricheaps, tb)
                        end
                    elseif tok isa BooleanTruth
                        if istop(tok)
                            close!(en)
                        elseif isbot(tok)
                            expand!(en)
                            push!(metricheaps, leaf) # Push leaf back into heap
                        end
                    else
                        error("Error: unrecognized token: ... ")
                    end
                end
            elseif tok isa NamedConnective{:∨}
                # Disjunction case
                expand!(en)
                for l ∈ findleaves(en)
                    (a, b) = subformulas(φ)
                    ta = Tableau(a, l)
                    tb = Tableau(b, l)
                    push!(metricheaps, ta)
                    push!(metricheaps, tb)
                end
            elseif tok isa NamedConnective{:∧}
                expand!(en)
                # Conjunction case
                for l ∈ findleaves(en)
                    (a, b) = subformulas(φ)
                    ta = Tableau(a, l)
                    tb = Tableau(b, ta)
                    push!(metricheaps, tb)
                end
            elseif tok isa NamedConnective{:→}
                expand!(en)
                # Implication case
                (a, b) = subformulas(φ)
                for l ∈ findleaves(en)
                    ta = Tableau(¬a, l)
                    tb = Tableau(b, l)
                    push!(metricheaps, ta)
                    push!(metricheaps, tb)
                end
            elseif tok isa BooleanTruth
                if istop(tok)
                    expand!(en)
                    push!(metricheaps, leaf) # Push leaf back into heap
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

Given a formula, return true if an interpretation that satisfies the formula
exists, false otherwise.

*choosenode* should be a function taking a vector of metricheaps as an argument
(and eventually a counter) and giving a tableau (or nothing) as output that is
used to extract a node representing a branch to be expanded. If nothing, all
branches are closed.

*metrics* should be functions taking a tableau as an argument and giving an
integer as output that are used to model the order in which tableau branches are 
xpanded. For example, one could declare the following metric functions:

    mf1(t::Tableau) = noperators(t.formula)
    mf2(t::Tableau) = height(t.formula)

The first metric will generate a metricheap proposing to expand first branches
comprising the node containing the formula with the less number of operators,
the second metric will generate a metricheap proposing to expand first branches
comprising the node containing the formula of less height.

*choosenode* will then be used to choose which policy to follow (e.g., choosing
the node voted by most heaps, or alternating between each heap at each cycle).
"""
function sat(
    formula::Formula,
    choosenode::F,
    metrics::Function...
) where {
    F<:Function
}
    metricheaps = Vector{MetricHeap}()   # Heaps used for tableau selection
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
    sat(
        formula::Formula,
        metric::F;
        rng = Random.GLOBAL_RNG
    ) where {
        F<:Function
    }

Given a formula and an extraction policy metric, return true if an
interpretation that satisfies the formula exists, false otherwise.

*metric* should be a function taking a tableau as an argument and giving an
integer as output that is used to model the order in which tableau branches are
expanded. For example, one could declare the following metric function:

    mf(t::Tableau) = noperators(t.formula)

This way, the tableau will be expanded giving precedence to branches comprising
nodes containing formulae with the smallest number operators.
"""
function sat(formula::Formula, metric::F; kwargs...) where {F<:Function}
    return sat(formula, roundrobin!, metric)
end

"""
    sat(formula::Formula; rng = Random.GLOBAL_RNG)

Given a formula, return true if an interpretation that satisfies the formula
exists, false otherwise.
"""
function sat(formula::Formula; rng = Random.GLOBAL_RNG, kwargs...)
    randombranch(_::Tableau) = rand(rng, Int)
    return sat(formula, randombranch)
end

"""
    sat(formula::Formula, choosenode::Function, metrics::Function...)

Given a formula, return true if it is valid, i.e., there is not an
interpretation that does not satisfy the formula, false otherwise.

*choosenode* should be a function taking a vector of metricheaps as an argument
(and eventually a counter) and giving a tableau (or nothing) as output that is
used to extract a node representing a branch to be expanded. If nothing, all
branches are closed.

*metrics* should be functions taking a tableau as an argument and giving an
integer as output that are used to model the order in which tableau branches are
expanded. For example, one could declare the following metric functions:

    mf1(t::Tableau) = noperators(t.formula)
    mf2(t::Tableau) = height(t.formula)

The first metric will generate a metricheap proposing to expand first branches
comprising the node containing the formula with the less number of operators,
the second metric will generate a metricheap proposing to expand first branches 
omprising the node containing the formula of less height.

*choosenode* will then be used to choose which policy to follow (e.g., choosing
the node voted by most heaps, or alternating between each heap at each cycle).
"""
function prove(
    formula::Formula,
    choosenode::F,
    metrics::Function...
) where {
    F<:Function
}
    metricheaps = Vector{MetricHeap}()   # Heaps used for tableau selection
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

Given a formula, return true if it is valid, i.e., there is not an
interpretation that does not satisfy the formula, false otherwise.

*metric* should be a function taking a tableau as an argument and giving an
integer as output that is used to model the order in which tableau branches are
expanded. For example, one could declare the following metric function:

    mf(t::Tableau) = noperators(t.formula)
    
This way, the tableau will be expanded giving precedence to branches comprising
nodes containing formulae with the smallest number operators.
"""
function prove(formula::Formula, metric::F; kwargs...) where {F<:Function}
    randombranch(_::Tableau) = rand(rng, Int)
    return prove(formula, roundrobin!, metric)
end

"""
    prove(formula::Formula; rng = Random.GLOBAL_RNG)

Given a formula, return true if it is valid, i.e., there is not an
interpretation that does not satisfy the formula, false otherwise.
"""
function prove(formula::Formula; rng = Random.GLOBAL_RNG, kwargs...)
    randombranch(_::Tableau) = rand(rng, Int)
    return prove(formula, randombranch)
end
