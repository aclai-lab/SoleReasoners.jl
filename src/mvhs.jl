struct Point
    label::String
end

Base.show(io::IO, x::Point) = print(io, x.label)

struct Interval
    x::Point
    y::Point
end

Base.show(io::IO, i::Interval) = print(io, "[$(i.x),$(i.y)]")

struct AFSLOS
    domain::Vector{Point}
    algebra::FiniteHeytingAlgebra
    mvlt::Dict{Tuple{Point,Point},FiniteTruth}
    mveq::Dict{Tuple{Point,Point},FiniteTruth}
end

"""
Check if a structure (D, <, =) is a adequate fuzzy strictly linearly ordered set.

1. =(x,y) = 1 iff x = y
2. =(x,y) = =(y,x)
3. <(x,x) = 0
4. <(x,z) ⪰ <(x,y)∩<(y,z)
5. if <(x,y) ≻ 0 and <(y,z) ≻ 0 then <(x,z) ≻ 0
6. if <(x,y) = 0 and <(y,x) = 0 then =(x,y) = 1
7. if =(x,y) ≻ 0 then <(x,y) ≺ 1
"""
function checkafslos(afslos::AFSLOS)
    # check axioms 1...7
    for x ∈ afslos.domain
        !istop(afslos.mveq[(x,x)]) && error("(D,<,=) is not a AFSLOS (1)")
        !isbot(afslos.mvlt[(x,x)]) && error("(D,<,=) is not a AFSLOS (3)")
        for y ∈ afslos.domain
            istop(afslos.mveq[(x,y)]) && x != y && error("(D,<,=) is not a AFSLOS (1)")
            afslos.mveq[(x,y)] != afslos.mveq[(y,x)] && error("(D,<,=) is not a AFSLOS (2)")
            if isbot(afslos.mvlt[(x,y)]) && isbot(afslos.mvlt[(y,x)])
                !istop(afslos.mveq[(x,y)]) && error("(D,<,=) is not a AFSLOS (6)")
            end
            if !isbot(afslos.mveq[(x,y)])
                istop(afslos.mvlt[(x,y)]) && error("(D,<,=) is not a AFSLOS (7)")
            end
            for z ∈ afslos.domain
                !succeedeq(
                    afslos.algebra,
                    afslos.mvlt[(x,z)],
                    afslos.algebra.meet(afslos.mvlt[(x,y)], afslos.mvlt[(y,z)])
                ) && error("(D,<,=) is not a AFSLOS (4)")
                if !isbot(afslos.mvlt[(x,y)]) && !isbot(afslos.mvlt[(y,z)])
                    isbot(afslos.mvlt[(x,z)]) && error("(D,<,=) is not a AFSLOS (5)")
                end
            end
        end
    end
end

mutable struct MVHSTableau <: AbstractTableau
    const judgement::Bool
    const boundingimplication::Union{
        Tuple{FiniteTruth,Formula},
        Tuple{Formula,FiniteTruth},
        Tuple{FiniteTruth,FiniteTruth}
    }
    const interval::Interval
    const constraintsystem::AFSLOS
    const father::Union{MVHSTableau,Nothing}
    children::Vector{MVHSTableau}
    expanded::Bool
    closed::Bool
end

isexpanded(t::MVHSTableau) = t.expanded
isclosed(t::MVHSTableau) = t.closed

expand!(t::MVHSTableau) = t.expanded = true
close!(t::MVHSTableau) = t.closed = true

function findexpansionnode(t::MVHSTableau)
    isnothing(t.father) || isexpanded(t.father) ? t : findexpansionnode(t.father)
end

function findleaves(leavesset::Vector{MVHSTableau}, t::MVHSTableau)
    if isempty(t.children)
        push!(leavesset, t)
    else
        for child ∈ children
            findleaves(leavesset, child)
        end
    end
    return leavesset
end

findleaves(t::MVHSTableau) = findleaves(Vector{MVHSTableau}(), t)

function Base.show(io::IO, t::MVHSTableau)
    print(
        io,
        "$(t.judgement)($(syntaxstring(t.boundingimplication[1])) ⪯ " *
        "$(syntaxstring(t.boundingimplication[2]))), $(t.interval), " *
        "C = (<: $(t.constraintsystem.mvlt), =: $(t.constraintsystem.mveq))"
    )
end

function mvhsalphasat(
    metricheaps::Vector{MetricHeap},
    choosenode::Function,
    algebra::FiniteHeytingAlgebra;
    verbose::Bool=false
) 
    cycle = 0
    while true
        node = choosenode(metricheaps, cycle)
        isnothing(node) && return false # all branches are closed
        if isexpanded(node) # found a satisfiable branch
            verbose && println(node) # print satisfiable branch
            return true
        end
        en = findexpansionnode(node)
        expand!(en)
        verbose && println(en)
        if en.boundingimplication isa Tuple{FiniteTruth, Formula}
            # T∧
            α = en.boundingimplication[1]
            φ = en.boundingimplication[2]
            if en.judgement && token(φ) isa NamedConnective{:∧} && !isbot(α)
                verbose && println("T∧")
                for l ∈ findleaves(en)
                    verbose && println(l)
                    t1 = MVHSTableau(
                        true,
                        (α, φ.children[1]),
                        en.interval,
                        l.constraintsystem,
                        l,
                        Vector{MVHSTableau}(),
                        false,
                        false
                    )
                    push!(metricheaps, t1)
                    verbose && println(t1)
                    t2 = MVHSTableau(
                        true,
                        (α, φ.children[2]),
                        en.interval,
                        l.constraintsystem,
                        t1,
                        Vector{MVHSTableau}(),
                        false,
                        false
                    )
                    push!(metricheaps, t2)
                    verbose && println(t2)
                    println()
                end
                return
            end
        end
    end
end

function mvhsalphasat(
    α::T,
    φ::Formula,
    algebra::FiniteHeytingAlgebra,
    choosenode::Function,
    metrics::Function...;
    verbose::Bool=false
) where {
    T<:Truth
}
    if !isa(α, FiniteTruth)
        α = convert(FiniteTruth, α)
    end
    tableaux = Vector{MVHSTableau}()
    x, y = Point.(["x", "y"])
    for δ ∈ getdomain(algebra)
        istop(δ) && continue    # (1)
        for β ∈ getdomain(algebra)
            isbot(β) && continue    # <(x,y) ≻ 0
            for γ ∈ getdomain(algebra)
                afslos = AFSLOS(
                    [x, y],
                    algebra,
                    Dict(
                        (x,x) => ⊥, (x,y) => β,
                        (y,x) => γ, (y,y) => ⊥
                    ),
                    Dict(
                        (x,x) => ⊤, (x,y) => δ,
                        (y,x) => δ, (y,y) => ⊤
                    )
                )
                try
                    checkafslos(afslos)
                    push!(
                        tableaux,
                        MVHSTableau(
                            true,
                            (α, φ),
                            Interval(x, y),
                            afslos,
                            nothing,
                            Vector{MVHSTableau}(),
                            false,
                            false
                        )
                    )
                catch err
                    verbose && println(sprint(showerror, err))
                end
            end
        end
    end
    verbose && println("Starting with $(length(tableaux)) tableaux")
    metricheaps = Vector{MetricHeap}()   # Heaps to be used for node selection
    for metric ∈ metrics
        push!(metricheaps, MetricHeap(metric))
    end
    for tableau ∈ tableaux
        for metricheap ∈ metricheaps
            push!(heap(metricheap), MetricHeapNode(metric(metricheap), tableau))
        end
    end
    mvhsalphasat(metricheaps, choosenode, algebra; verbose)
end

function mvhsalphasat(
    α::T,
    φ::Formula,
    algebra::FiniteHeytingAlgebra,
    metric::Function;
    verbose::Bool=false
) where {
    T<:Truth
}
    mvhsalphasat(α, φ, algebra, roundrobin, metric; verbose)
end

function mvhsalphasat(
    α::T,
    φ::Formula,
    algebra::FiniteHeytingAlgebra;
    rng = Random.GLOBAL_RNG,
    verbose::Bool=false
) where {
    T<:Truth
}
    randombranch(_::MVHSTableau) = rand(rng, Int)
    mvhsalphasat(α, φ, algebra, randombranch; verbose)
end
