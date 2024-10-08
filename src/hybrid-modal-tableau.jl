mutable struct HybridMVHSTableau{T<:Truth} <: AbstractTableau
    const judgement::Bool
    const boundingimplication::Union{
        Tuple{T,Formula},
        Tuple{Formula,T},
        Tuple{T,T}
    }
    const interval::Interval
    constraintsystem::Union{AFSLOS,Nothing}
    const father::Union{HybridMVHSTableau,Nothing}
    children::Vector{HybridMVHSTableau}
    expanded::Bool
    closed::Bool

    function HybridMVHSTableau{T}(
        judgement::Bool,
        boundingimplication::Union{
            Tuple{T1,Formula},
            Tuple{Formula,T1},
            Tuple{T1,T2}
        },
        interval::Interval
    ) where {
        T<:Truth,
        T1<:Truth,
        T2<:Truth
    }
        if isa(boundingimplication, Tuple{T1,Formula})
            if !isa(boundingimplication, Tuple{T,Formula})
                boundingimplication = (
                    convert(T, boundingimplication[1]),
                    boundingimplication[2]
                )
            end
        elseif isa(boundingimplication, Tuple{Formula,T1})
            if !isa(boundingimplication, Tuple{Formula,T})
                boundingimplication = (
                    boundingimplication[1],
                    convert(T, boundingimplication[2]),
                )
            end
        elseif isa(boundingimplication, Tuple{T1,T2})
            if !isa(boundingimplication, Tuple{T,T})
                boundingimplication = (
                    convert(T, boundingimplication[1]),
                    convert(T, boundingimplication[2]),
                )
            end
        else
            error("Unexpected error")
        end
        return new{T}(
            judgement,
            boundingimplication,
            interval,
            nothing,
            nothing,
            Vector{HybridMVHSTableau}(),
            false,
            false
        )
    end

    function HybridMVHSTableau{T}(
        judgement::Bool,
        boundingimplication::Union{
            Tuple{T1,Formula},
            Tuple{Formula,T1},
            Tuple{T1,T2}
        },
        interval::Interval,
        constraintsystem::AFSLOS
    ) where{
        T<:Truth,
        T1<:Truth,
        T2<:Truth
    }
        if isa(boundingimplication, Tuple{T1,Formula})
            if !isa(boundingimplication, Tuple{T,Formula})
                boundingimplication = (
                    convert(T, boundingimplication[1]),
                    boundingimplication[2]
                )
            end
        elseif isa(boundingimplication, Tuple{Formula,T1})
            if !isa(boundingimplication, Tuple{Formula,T})
                boundingimplication = (
                    boundingimplication[1],
                    convert(T, boundingimplication[2]),
                )
            end
        elseif isa(boundingimplication, Tuple{T1,T2})
            if !isa(boundingimplication, Tuple{T,T})
                boundingimplication = (
                    convert(T, boundingimplication[1]),
                    convert(T, boundingimplication[2]),
                )
            end
        else
            error("Unexpected error")
        end
        return new{T}(
            judgement,
            boundingimplication,
            interval,
            constraintsystem,
            nothing,
            Vector{HybridMVHSTableau}(),
            false,
            false
        )
    end

    function HybridMVHSTableau{T}(
        judgement::Bool,
        boundingimplication::Union{
            Tuple{T1,Formula},
            Tuple{Formula,T1},
            Tuple{T1,T2}
        },
        interval::Interval,
        constraintsystem::AFSLOS,
        father::HybridMVHSTableau
    ) where{
        T<:Truth,
        T1<:Truth,
        T2<:Truth
    }
        if isa(boundingimplication, Tuple{T1,Formula})
            if !isa(boundingimplication, Tuple{T,Formula})
                boundingimplication = (
                    convert(T, boundingimplication[1]),
                    boundingimplication[2]
                )
            end
        elseif isa(boundingimplication, Tuple{Formula,T1})
            if !isa(boundingimplication, Tuple{Formula,T})
                boundingimplication = (
                    boundingimplication[1],
                    convert(T, boundingimplication[2]),
                )
            end
        elseif isa(boundingimplication, Tuple{T1,T2})
            if !isa(boundingimplication, Tuple{T,T})
                boundingimplication = (
                    convert(T, boundingimplication[1]),
                    convert(T, boundingimplication[2]),
                )
            end
        else
            error("Unexpected error")
        end
        t = new{T}(
            judgement,
            boundingimplication,
            interval,
            constraintsystem,
            father,
            Vector{HybridMVHSTableau}(),
            false,
            false
        )
        pushchildren!(father, t)
        return t
    end
end

isroot(t::HybridMVHSTableau) = isnothing(t.father)
isleaf(t::HybridMVHSTableau) = isempty(t.children)
isexpanded(t::HybridMVHSTableau) = t.expanded
isclosed(t::HybridMVHSTableau) = t.closed

expand!(t::HybridMVHSTableau) = t.expanded = true

function close!(t::HybridMVHSTableau)
    t.closed = true
    while !isempty(t.children)
        c = pop!(t.children)
        close!(c)
    end
end

function pushchildren!(t::HybridMVHSTableau, children::HybridMVHSTableau...)
    push!(t.children, children...)
end

function findexpansionnode(t::HybridMVHSTableau)
    isroot(t) || isexpanded(t.father) ? t : findexpansionnode(t.father)
end

function findleaves(leavesset::Vector{HybridMVHSTableau}, t::HybridMVHSTableau)
    if isempty(t.children)
        push!(leavesset, t)
    else
        for child ∈ t.children
            findleaves(leavesset, child)
        end
    end
    return leavesset
end

findleaves(t::HybridMVHSTableau) = findleaves(Vector{HybridMVHSTableau}(), t)

function Base.show(io::IO, t::HybridMVHSTableau)
    if isnothing(t.constraintsystem)
        print(
            io,
            "$(t.judgement)("*
            "$(syntaxstring(t.boundingimplication[1], remove_redundant_parentheses=false))"*
            " ⪯ "*
            "$(syntaxstring(t.boundingimplication[2], remove_redundant_parentheses=false))"*
            "), $(t.interval), C = *\n"
        )
    else
        print(
            io,
            "$(t.judgement)($(syntaxstring(t.boundingimplication[1])) ⪯ "*
            "$(syntaxstring(t.boundingimplication[2]))), $(t.interval), "*
            "C = (\n\t<: $(t.constraintsystem.mvlt),\n\t=: $(t.constraintsystem.mveq)\n)"
        )
    end
end

function findsimilar(
    t::HybridMVHSTableau,
    a::A
) where {
    T<:Truth,
    D<:AbstractVector{T},
    A<:FiniteAlgebra{T,D}
}
    ψ = t.boundingimplication[2]
    if t.judgement
        γ = t.boundingimplication[1]
        # Looking for F(α⪯ψ) where α⪯β
        while !isroot(t)
            t = t.father
            β = t.boundingimplication[1]
            if β isa Truth && t.boundingimplication[2] == ψ && !t.judgement && precedeq(a, β, γ)
                return true
            end
        end
    else
        β = t.boundingimplication[1]
        # Looking for T(β⪯ψ) where α⪯β
        while !isroot(t)
            t = t.father
            γ = t.boundingimplication[1]
            if γ isa Truth && t.boundingimplication[2] == ψ && t.judgement && precedeq(a, β, γ)
                return true
            end
        end
    end
    return false
end

function findformula(
    t::HybridMVHSTableau,
    j::Bool,
    φ::Union{
        Tuple{T,Formula},
        Tuple{Formula,T},
        Tuple{T,T}
    }
) where {
    T<:Truth
}
    t.judgement == j && t.boundingimplication == φ && return true
    while !isroot(t)
        t = t.father
        t.judgement == j && t.boundingimplication == φ && return true
    end
    return false
end

"""
Return true if there is a HybridMVHSTableau (j,φ,i) is the path from t to the root
"""
function findtableau(
    t::HybridMVHSTableau,
    j::Bool,
    φ::Union{
        Tuple{T,Formula},
        Tuple{Formula,T},
        Tuple{T,T}
    },
    i::Interval,
    # c::AFSLOS
) where {
    T<:Truth
}
    # t.judgement == j && t.boundingimplication == φ && t.interval == i && equal(t.constraintsystem,c) && return true
    t.judgement == j && t.boundingimplication == φ && t.interval == i && return true
    while !isroot(t)
        t = t.father
        # t.judgement == j && t.boundingimplication == φ && t.interval == i && equal(t.constraintsystem,c) && return true
        t.judgement == j && t.boundingimplication == φ && t.interval == i && return true
    end
    return false
end

removecs!(t::HybridMVHSTableau) = t.constraintsystem = nothing

function printsolution(t::HybridMVHSTableau)
    sol = Vector{HybridMVHSTableau}()
    push!(sol, t)
    while !isroot(t)
        t = t.father
        push!(sol, t)
    end
    for s in reverse(sol)
        println(s)
    end
end

function cleancss!(tableaux::Vector{HybridMVHSTableau})
    for t in tableaux
        for l in findleaves(t)
            n = l
            while !isroot(n)
                if !isleaf(n)
                    removecs!(n)
                end
                n = n.father
            end
        end
    end
end

function hybridmvhsalphasat(
    metricheaps::Vector{MetricHeap},
    choosenode::Function,
    a::FiniteFLewAlgebra{T,D},
    roots::Vector{HybridMVHSTableau};
    verbose::Bool=false,
    timeout::Union{Nothing,Int}=nothing,
    diamondexpansion::Float64=1.0
) where {
    T<:Truth,
    D<:AbstractVector{T}
}
    cycle = 0
    t0 = time_ns()
    while true
        
        if cycle%1e2==0
            cleanheaps!(metricheaps)
            # cleancss!(roots)
        end

        # if timeout, return false with a warning
        if !isnothing(timeout) && (time_ns()-t0)/1e9 > timeout
            verbose && println("Timeout")
            return nothing
        end

        # if using too much memory, try to free memory calling full GC sweep
        if cycle%10==0 && getfreemem() < gettotmem()*5e-2
            verbose && println("Calling Garbage Collector")
            GC.gc()
        end
        # if using too much memory, kill execution to avoid crashes
        if cycle%10==0 && getfreemem() < gettotmem()*5e-2
            verbose && println("Too much memory being used, exiting")
            return nothing
        end

        node = choosenode(metricheaps, cycle)
        isnothing(node) && return false # all branches are closed
        isexpanded(node) && return true # found a satisfiable branch
        en = findexpansionnode(node)
        expand!(en)
        verbose && println("expansion node:")
        verbose && println(en)
        if en.boundingimplication isa Tuple{Truth, Truth}
            β = en.boundingimplication[1]
            γ = en.boundingimplication[2]
            if en.judgement && !precedeq(a, β, γ)
                # X1
                verbose && println("X1")
                close!(en)
            elseif !en.judgement && precedeq(a, β, γ)
                # X2
                verbose && println("X2")
                close!(en)
            elseif !en.judgement && isbot(β)
                # X3
                verbose && println("X3")
                close!(en)
            elseif !en.judgement && istop(γ)
                # X4
                verbose && println("X4")
                close!(en)
            elseif findsimilar(en, a)
                # X5
                verbose && println("X5")
                close!(en)
            else
                # let err
                #     try
                #         checkafslos(en.constraintsystem)
                #     catch err
                #         # X6
                #         verbose && println(sprint(showerror, err))
                #         verbose && println("X6")
                #         close!(en)
                #     end
                # end
                # No condition matched, pushing node back into metricheaps
                push!(metricheaps, node)
            end
        elseif en.boundingimplication isa Tuple{Truth, Formula}
            β = en.boundingimplication[1]
            φ = en.boundingimplication[2]
            if !en.judgement && isbot(β)
                # X3
                verbose && println("X3")
                close!(en)                
            elseif findsimilar(en, a)
                # X5
                verbose && println("X5")
                close!(en)
            elseif en.judgement && token(φ) isa NamedConnective{:∧} && !isbot(β)
                # T∧                
                (ψ, ε) = children(φ)
                # Search for support tuples
                pairs = Set{NTuple{2,T}}()
                for βi ∈ getdomain(a)
                    for γi ∈ getdomain(a)
                        if precedeq(a, β, a.monoid(βi, γi))
                            push!(pairs, (βi, γi))
                        end
                    end
                end
                for p ∈ pairs
                    for q ∈ pairs
                        if precedeq(a, q[1], p[1]) && precedeq(a, q[2], p[2]) && p != q
                            delete!(pairs, p)
                        end
                    end
                end
                for l ∈ findleaves(en)
                    newnodes = false
                    for pair ∈ pairs
                        newnodes = true
                        if !findtableau(l, true, (pair[1], ψ), en.interval)
                            t1 = HybridMVHSTableau{T}(
                            true,
                            (pair[1], ψ),
                            en.interval,
                            l.constraintsystem,
                            l
                        )
                            push!(metricheaps, t1)
                            if !findtableau(t1, true, (pair[2], ε), en.interval)
                                    t2 = HybridMVHSTableau{T}(
                                    true,
                                    (pair[2], ε),
                                    en.interval,
                                    t1.constraintsystem,
                                    t1
                                )
                                push!(metricheaps, t2)
                            end
                        else
                            if !findtableau(l, true, (pair[2], ε), en.interval)
                                newnodes = true
                                t2 = HybridMVHSTableau{T}(
                                    true,
                                    (pair[2], ε),
                                    en.interval,
                                    l.constraintsystem,
                                    l
                                )
                                push!(metricheaps, t2)
                            else  # Here there should be a branch and I need to keep track of it
                                ti = HybridMVHSTableau{T}(   # Fake node (always true)
                                    true,
                                    (⊤, ⊤),
                                    en.interval,
                                    l.constraintsystem,
                                    l
                                )
                                push!(metricheaps, ti)
                            end
                        end
                    end
                    !newnodes && l == node && push!(metricheaps, node)
                end
            elseif !en.judgement && token(φ) isa NamedConnective{:∧} && !isbot(β)
                # F∧
                (ψ, ε) = children(φ)
                # Search for support tuples
                pairs = Set{NTuple{2,T}}()
                for βi ∈ getdomain(a)
                    for γi ∈ getdomain(a)
                        if !precedeq(a, β, a.monoid(βi, γi))
                            push!(pairs, (βi, γi))
                        end
                    end
                end
                for p in pairs
                    for q in pairs
                        if precedeq(a, p[1], q[1]) && precedeq(a, p[2], q[2]) && p != q
                            delete!(pairs, p)
                        end
                    end
                end
                for l ∈ findleaves(en)
                    newnodes = false
                    for pair in pairs
                        newnodes = true
                        if !findtableau(l, true, (ψ, pair[1]), en.interval)
                            t1 = HybridMVHSTableau{T}(
                                true,
                                (ψ, pair[1]),
                                en.interval,
                                l.constraintsystem,
                                l
                            )
                            push!(metricheaps, t1)
                            if !findtableau(t1, true, (ε, pair[2]), en.interval)
                                t2 = HybridMVHSTableau{T}(
                                    true,
                                    (ε, pair[2]),
                                    en.interval,
                                    t1.constraintsystem,
                                    t1
                                )
                                push!(metricheaps, t2)
                            end
                        else
                            if !findtableau(l, true, (ε, pair[2]), en.interval)
                                t2 = HybridMVHSTableau{T}(
                                    true,
                                    (ε, pair[2]),
                                    en.interval,
                                    l.constraintsystem,
                                    l
                                )
                                push!(metricheaps, t2)
                            else  # Here there should be a branch and I need to keep track of it
                                ti = HybridMVHSTableau{T}(   # Fake node (always true)
                                    true,
                                    (⊤, ⊤),
                                    en.interval,
                                    l.constraintsystem,
                                    l
                                )
                                push!(metricheaps, ti)
                            end
                        end
                    end
                    !newnodes && l == node && push!(metricheaps, node)
                end
            elseif en.judgement && token(φ) isa NamedConnective{:→} && !isbot(β)
                # T→
                (ψ, ε) = children(φ)
                # Search for support tuples
                pairs = Set{NTuple{2,T}}()
                for βi ∈ getdomain(a)
                    for γi ∈ getdomain(a)
                        if precedeq(a, β, a.implication(βi, γi))
                            push!(pairs, (βi, γi))
                        end
                    end
                end
                for p in pairs
                    for q in pairs
                        if precedeq(a, p[1], q[1]) && precedeq(a, q[2], p[2]) && p != q
                            delete!(pairs, p)
                        end
                    end
                end
                for l ∈ findleaves(en)
                    newnodes = false
                    for pair in pairs
                        newnodes = true
                        if !findtableau(l, true, (ψ, pair[1]), en.interval)
                            t1 = HybridMVHSTableau{T}(
                                true,
                                (ψ, pair[1]),
                                en.interval,
                                l.constraintsystem,
                                l
                            )
                            push!(metricheaps, t1)
                            if !findtableau(t1, true, (pair[2], ε), en.interval)
                                    t2 = HybridMVHSTableau{T}(
                                    true,
                                    (pair[2], ε),
                                    en.interval,
                                    t1.constraintsystem,
                                    t1
                                )
                                push!(metricheaps, t2)
                            end
                        else
                            if !findtableau(l, true, (pair[2], ε), en.interval)
                                t2 = HybridMVHSTableau{T}(
                                    true,
                                    (pair[2], ε),
                                    en.interval,
                                    l.constraintsystem,
                                    l
                                )
                                push!(metricheaps, t2)
                            else  # Here there should be a branch and I need to keep track of it
                                ti = HybridMVHSTableau{T}(   # Fake node (always true)
                                    true,
                                    (⊤, ⊤),
                                    en.interval,
                                    l.constraintsystem,
                                    l
                                )
                                push!(metricheaps, ti)
                            end
                        end
                    end
                    !newnodes && l == node && push!(metricheaps, node)
                end
            elseif !en.judgement && token(φ) isa NamedConnective{:→} && !isbot(β)
                # F→
                (ψ, ε) = children(φ)
                # Search for support tuples
                pairs = Set{NTuple{2,T}}()
                for βi ∈ getdomain(a)
                    for γi ∈ getdomain(a)
                        if !precedeq(a, β, a.implication(βi, γi))
                            push!(pairs, (βi, γi))
                        end
                    end
                end
                for p in pairs
                    for q in pairs
                        if precedeq(a, q[1], p[1]) && precedeq(a, p[2], q[2]) && p != q
                            delete!(pairs, p)
                        end
                    end
                end
                for l ∈ findleaves(en)
                    newnodes = false
                    for pair in pairs
                        newnodes = true
                        if !findtableau(l, true, (pair[1], ψ), en.interval)
                            t1 = HybridMVHSTableau{T}(
                                true,
                                (pair[1], ψ),
                                en.interval,
                                l.constraintsystem,
                                l
                            )
                            push!(metricheaps, t1)
                            if !findtableau(t1, true, (ε, pair[2]), en.interval)
                                t2 = HybridMVHSTableau{T}(
                                    true,
                                    (ε, pair[2]),
                                    en.interval,
                                    t1.constraintsystem,
                                    t1
                                )
                                push!(metricheaps, t2)
                            end
                        else
                            if !findtableau(l, true, (ε, pair[2]), en.interval)
                                t2 = HybridMVHSTableau{T}(
                                    true,
                                    (ε, pair[2]),
                                    en.interval,
                                    l.constraintsystem,
                                    l
                                )
                                push!(metricheaps, t2)
                            else  # Here there should be a branch and I need to keep track of it
                                ti = HybridMVHSTableau{T}(   # Fake node (always true)
                                    true,
                                    (⊤, ⊤),
                                    en.interval,
                                    l.constraintsystem,
                                    l
                                )
                                push!(metricheaps, ti)
                            end
                        end
                    end
                    !newnodes && l == node && push!(metricheaps, node)
                end
            elseif en.judgement && token(φ) isa BoxRelationalConnective
                # T□"
                verbose && println("T□")
                for l ∈ findleaves(en)
                    r = SoleLogics.relation(token(φ))
                    (x, y) = (en.interval.x, en.interval.y)
                    cB = l.constraintsystem
                    tj = l
                    for zi ∈ cB.domain
                        for ti ∈ cB.domain
                            isbot(cB.mvlt[(zi,ti)]) && continue # <(zi,ti) ≻ 0
                            βi = mveval(r, (x,y), (zi,ti), cB)
                            if !isbot(βi) && precedeq(a, β, a.meet(β, βi))
                                # Optimization 1 (int. node)
                                if !findtableau(tj,true,(a.meet(β, βi), φ.children[1]),Interval(zi,ti))
                                    tj = HybridMVHSTableau{T}(
                                        true,
                                        (a.meet(β, βi), φ.children[1]),
                                        Interval(zi,ti),
                                        cB,
                                        tj
                                    )
                                    push!(metricheaps, tj)
                                end                                
                            end
                        end
                    end
                    # Optimization 2 (leaf node)
                    if en == l == tj
                        verbose && printsolution(en)
                        return true # found satisfiable branch
                    else
                        tj = HybridMVHSTableau{T}(
                            true,
                            (β, φ),
                            en.interval,
                            cB,
                            tj
                        )
                        push!(metricheaps, tj)
                    end
                end
            elseif !en.judgement && token(φ) isa BoxRelationalConnective
                # F□"
                verbose && println("F□")
                for l ∈ findleaves(en)
                    r = SoleLogics.relation(token(φ))
                    (x, y) = (en.interval.x, en.interval.y)
                    cB0 = l.constraintsystem

                    # cB0 = o(cB)
                    for zi ∈ cB0.domain
                        for ti ∈ cB0.domain
                            isbot(cB0.mvlt[(zi,ti)]) && continue # <(zi,ti) ≻ 0
                            βi = mveval(r, (x,y), (zi,ti), cB0)
                            if !isbot(βi) && precedeq(a, β, a.meet(β, βi))
                                tj = HybridMVHSTableau{T}(
                                    false,
                                    (a.meet(βi, β), φ.children[1]),
                                    Interval(zi,ti),
                                    cB0,
                                    l
                                )
                                push!(metricheaps, tj)
                            end
                        end
                    end

                    u = Threads.SpinLock();

                    # All possible combinations of values for new tuples (+ % d.e. opt.)
                    # TODO: fully expand first cycle
                    combs = reshape(
                        collect(Iterators.product((getdomain(a) for p ∈ cB0.domain)...)),
                        (1,:)
                    )
                    ncombs = length(combs)
                    Threads.@threads for ltzcombs ∈ shuffle(combs)[1:floor(Int, ncombs*diamondexpansion)]
                        for gtzcombs ∈ shuffle(combs)[1:floor(Int, ncombs*diamondexpansion)]
                            for eqzcombs ∈ shuffle(combs)[1:floor(Int, ncombs*diamondexpansion)]
                                # Must initialize at every (parallel) cycle!
                                # cB1 = o(cB) ∪ {z}
                                z = Point(Char(Int(last(cB0.domain).label)+1))
                                cB1 = AFSLOS(
                                    vcat(cB0.domain, z),
                                    cB0.algebra,
                                    Dict(cB0.mvlt),
                                    Dict(cB0.mveq)
                                )
                                cB1.mvlt[(z,z)] = ⊥
                                cB1.mveq[(z,z)] = ⊤
            
                                # cB2 = cB1 ∪ {t} = o(cB) ∪ {z,t}
                                t = Point(Char(Int(last(cB1.domain).label)+1))

                                for i ∈ 1:length(cB0.domain)
                                    cB1.mvlt[(cB0.domain[i],z)] = ltzcombs[i]
                                    cB1.mvlt[(z,cB0.domain[i])] = gtzcombs[i]
                                    cB1.mveq[(cB0.domain[i],z)] = eqzcombs[i]
                                    cB1.mveq[(z,cB0.domain[i])] = eqzcombs[i]
                                end
                                try
                                    checkafslos(cB1)
                                    # in general, < is not commutative!
                                    for zi ∈ cB0.domain
                                        isbot(cB1.mvlt[(zi,z)]) && continue # <(zi,z) ≻ 0
                                        βi = mveval(r, (x,y), (zi,z), cB1)
                                        if !isbot(βi) && precedeq(a, β, a.meet(β, βi))
                                            Threads.lock(u) do
                                                tj = HybridMVHSTableau{T}(
                                                    false,
                                                    (a.meet(βi, β), φ.children[1]),
                                                    Interval(zi,z),
                                                    cB1,
                                                    l
                                                )
                                                push!(metricheaps, tj)
                                            end
                                        end
                                    end
                                    for ti ∈ cB0.domain
                                        isbot(cB1.mvlt[(z,ti)]) && continue # <(z,ti) ≻ 0
                                        βi = mveval(r, (x,y), (z,ti), cB1)
                                        if !isbot(βi) && precedeq(a, β, a.meet(β, βi))
                                            Threads.lock(u) do
                                                tj = HybridMVHSTableau{T}(
                                                    false,
                                                    (a.meet(βi, β), φ.children[1]),
                                                    Interval(z,ti),
                                                    cB1,
                                                    l
                                                )
                                                push!(metricheaps, tj)
                                            end
                                        end
                                    end

                                    # cB2 = cB1 ∪ {t} = o(cB) ∪ {z,t}
                                    cB2 = AFSLOS(
                                        vcat(cB1.domain, t),
                                        cB1.algebra,
                                        Dict(cB1.mvlt),
                                        Dict(cB1.mveq)
                                    )
                                    cB2.mvlt[(t,t)] = ⊥
                                    cB2.mveq[(t,t)] = ⊤

                                    # All possible combinations of values for new tuples
                                    for lttcombs ∈ reshape(
                                        collect(Iterators.product((getdomain(a) for p ∈ cB1.domain)...)),
                                        (1,:)
                                    )
                                        for gttcombs ∈ reshape(
                                            collect(Iterators.product((getdomain(a) for p ∈ cB1.domain)...)),
                                            (1,:)
                                        )
                                            for eqtcombs ∈ reshape(
                                                collect(Iterators.product((getdomain(a) for p ∈ cB1.domain)...)),
                                                (1,:)
                                            )
                                                for i ∈ 1:length(cB1.domain)
                                                    cB2.mvlt[(cB1.domain[i],t)] = lttcombs[i]
                                                    cB2.mvlt[(t,cB1.domain[i])] = gttcombs[i]
                                                    cB2.mveq[(cB1.domain[i],t)] = eqtcombs[i]
                                                    cB2.mveq[(t,cB1.domain[i])] = eqtcombs[i]
                                                end
                                                isbot(cB2.mvlt[(z,t)]) && isbot(cB2.mvlt[(t,z)]) && continue
                                                try
                                                    checkafslos(cB2)
                                                    # in general, < is not commutative!
                                                    if !isbot(cB2.mvlt[(z,t)])  # <(z,t) ≻ 0
                                                        βi = mveval(r, (x,y), (z,t), cB2)
                                                        if !isbot(βi) && precedeq(a, β, a.meet(β, βi))
                                                            Threads.lock(u) do
                                                                tj = HybridMVHSTableau{T}(
                                                                    false,
                                                                    (a.meet(βi, β), φ.children[1]),
                                                                    Interval(z,t),
                                                                    cB2,
                                                                    l
                                                                )
                                                                push!(metricheaps, tj)
                                                            end
                                                        end
                                                    else    # <(t,z) ≻ 0
                                                        βi = mveval(r, (x,y), (t,z), cB2)
                                                        if !isbot(βi) && precedeq(a, β, a.meet(β, βi))
                                                            Threads.lock(u) do
                                                                tj = HybridMVHSTableau{T}(
                                                                    false,
                                                                    (a.meet(βi, β), φ.children[1]),
                                                                    Interval(t,z),
                                                                    cB2,
                                                                    l
                                                                )
                                                                push!(metricheaps, tj)
                                                            end
                                                        end
                                                    end
                                                catch err2
                                                    verbose && println(sprint(showerror, err2))
                                                end
                                            end
                                        end
                                    end
                                catch err1
                                    verbose && println(sprint(showerror, err1))
                                end
                            end
                        end
                    end
                end
            elseif en.judgement && !isbot(β)
                # T⪰
                verbose && println("T⪰")
                for l ∈ findleaves(en)
                    ti = l
                    newnodes = false
                    for γ in maximalmembers(a, β)
                        if !findtableau(ti, false, (φ, γ), en.interval)
                            newnodes = true
                            ti = HybridMVHSTableau{T}(
                                false,
                                (φ, γ),
                                en.interval,
                                l.constraintsystem,
                                ti
                            )
                            push!(metricheaps, ti)
                        end
                    end
                    !newnodes && l == node && push!(metricheaps, node)
                end
            elseif !en.judgement && !isbot(β)
                # F⪰
                verbose && println("F⪰")
                for l ∈ findleaves(en)
                    newnodes = false
                    for βi in maximalmembers(a, β)
                        newnodes = true
                        if !findtableau(l, true, (φ, βi), en.interval)
                            ti = HybridMVHSTableau{T}(
                                true,
                                (φ, βi),
                                en.interval,
                                l.constraintsystem,
                                l
                            )
                            push!(metricheaps, ti)
                        else  # Here there should be a branch and I need to keep track of it
                            ti = HybridMVHSTableau{T}(   # Fake node (always true)
                                true,
                                (⊤, ⊤),
                                en.interval,
                                l.constraintsystem,
                                l
                            )
                            push!(metricheaps, ti)
                        end
                    end
                    !newnodes && l == node && push!(metricheaps, node)
                end
            else
                # No condition matched, pushing node back into metricheaps
                push!(metricheaps, node)
            end
        elseif en.boundingimplication isa Tuple{Formula, Truth}
            φ = en.boundingimplication[1]
            β = en.boundingimplication[2]
            if !en.judgement && istop(β)
                # X4
                verbose && println("X4")
                close!(en)
            elseif en.judgement && token(φ) isa NamedConnective{:∨} && !istop(β)
                # T∨
                (ψ, ε) = children(φ)
                # Search for support tuples
                pairs = Set{NTuple{2,T}}()
                for βi ∈ getdomain(a)
                    for γi ∈ getdomain(a)
                        if precedeq(a, a.join(βi, γi), β)
                            push!(pairs, (βi, γi))
                        end
                    end
                end
                for p in pairs
                    for q in pairs
                        if precedeq(a, p[1], q[1]) && precedeq(a, p[2], q[2]) && p != q
                            delete!(pairs, p)
                        end
                    end
                end
                for l ∈ findleaves(en)
                    newnodes = false
                    for pair in pairs
                        newnodes = true
                        if !findtableau(l, true, (ψ, pair[1]), en.interval)
                            t1 = HybridMVHSTableau{T}(
                                true,
                                (ψ, pair[1]),
                                en.interval,
                                l.constraintsystem,
                                l
                            )
                            push!(metricheaps, t1)
                            if !findtableau(t1, true, (ε, pair[2]), en.interval)
                                t2 = HybridMVHSTableau{T}(
                                    true,
                                    (ε, pair[2]),
                                    en.interval,
                                    t1.constraintsystem,
                                    t1
                                )
                                push!(metricheaps, t2)
                            end
                        else
                            if !findtableau(l, true, (ε, pair[2]), en.interval)
                                t2 = HybridMVHSTableau{T}(
                                    true,
                                    (ε, pair[2]),
                                    en.interval,
                                    l.constraintsystem,
                                    l
                                )
                                push!(metricheaps, t2)
                            else  # Here there should be a branch and I need to keep track of it
                                ti = HybridMVHSTableau{T}(   # Fake node (always true)
                                    true,
                                    (⊤, ⊤),
                                    en.interval,
                                    l.constraintsystem,
                                    l
                                )
                                push!(metricheaps, ti)
                            end
                        end
                    end
                    !newnodes && l == node && push!(metricheaps, node)
                end
            elseif !en.judgement && token(φ) isa NamedConnective{:∨} && !istop(β)
                # F∨
                (ψ, ε) = children(φ)
                # Search for support tuples
                pairs = Set{NTuple{2,T}}()
                for βi ∈ getdomain(a)
                    for γi ∈ getdomain(a)
                        if !precedeq(a, a.join(βi, γi), β)
                            push!(pairs, (βi, γi))
                        end
                    end
                end
                for p in pairs
                    for q in pairs
                        if precedeq(a, q[1], p[1]) && precedeq(a, q[2], p[2]) && p != q
                            delete!(pairs, p)
                        end
                    end
                end
                for l ∈ findleaves(en)
                    newnodes = false
                    for pair in pairs
                        newnodes = true
                        if !findtableau(l, true, (pair[1], ψ), en.interval)
                            t1 = HybridMVHSTableau{T}(
                                true,
                                (pair[1], ψ),
                                en.interval,
                                l.constraintsystem,
                                l
                            )
                            push!(metricheaps, t1)
                            if !findtableau(l, true, (pair[2], ε), en.interval)
                                t2 = HybridMVHSTableau{T}(
                                    true,
                                    (pair[2], ε),
                                    en.interval,
                                    t1.constraintsystem,
                                    t1
                                )
                                push!(metricheaps, t2)
                            end
                        else
                            if !findtableau(l, true, (pair[2], ε), en.interval)
                                t2 = HybridMVHSTableau{T}(
                                    true,
                                    (pair[2], ε),
                                    en.interval,
                                    l.constraintsystem,
                                    l
                                )
                                push!(metricheaps, t2)
                            else  # Here there should be a branch and I need to keep track of it
                                ti = HybridMVHSTableau{T}(   # Fake node (always true)
                                    true,
                                    (⊤, ⊤),
                                    en.interval,
                                    l.constraintsystem,
                                    l
                                )
                                push!(metricheaps, ti)
                            end
                        end
                    end
                    !newnodes && l == node && push!(metricheaps, node)
                end
            elseif en.judgement && token(φ) isa DiamondRelationalConnective
                # T◊"
                verbose && println("T◊")
                for l ∈ findleaves(en)
                    r = SoleLogics.relation(token(φ))
                    (x, y) = (en.interval.x, en.interval.y)
                    cB = l.constraintsystem
                    tj = l
                    for zi ∈ cB.domain
                        for ti ∈ cB.domain
                            isbot(cB.mvlt[(zi,ti)]) && continue # <(zi,ti) ≻ 0
                            βi = mveval(r, (x,y), (zi,ti), cB)
                            if !isbot(βi) && precedeq(a, a.implication(βi, β), β)
                                # Optimization 1 (int. node)
                                if !findtableau(tj,true,(φ.children[1], a.implication(βi, β)),Interval(zi,ti))
                                    tj = HybridMVHSTableau{T}(
                                        true,
                                        (φ.children[1], a.implication(βi, β)),
                                        Interval(zi,ti),
                                        cB,
                                        tj
                                    )
                                    push!(metricheaps, tj)
                                end
                            end
                        end
                    end
                    # Optimization 2 (leaf node)
                    if en == l == tj
                        verbose && printsolution(en)
                        return true # found satisfiable branch
                    else
                        tj = HybridMVHSTableau{T}(
                            true,
                            (φ, β),
                            en.interval,
                            cB,
                            tj
                        )
                        push!(metricheaps, tj)
                    end
                end
            elseif !en.judgement && token(φ) isa DiamondRelationalConnective
                # F◊
                verbose && println("F◊")
                for l ∈ findleaves(en)
                    r = SoleLogics.relation(token(φ))
                    (x, y) = (en.interval.x, en.interval.y)
                    cB0 = l.constraintsystem

                    # cB0 = o(cB)
                    for zi ∈ cB0.domain
                        for ti ∈ cB0.domain
                            isbot(cB0.mvlt[(zi,ti)]) && continue # <(zi,ti) ≻ 0
                            βi = mveval(r, (x,y), (zi,ti), cB0)
                            if !isbot(βi) && precedeq(a, a.implication(βi, β), β)
                                tj = HybridMVHSTableau{T}(
                                    false,
                                    (φ.children[1], a.implication(βi, β)),
                                    Interval(zi,ti),
                                    cB0,
                                    l
                                )
                                push!(metricheaps, tj)
                            end
                        end
                    end

                    u = Threads.SpinLock();

                    # All possible combinations of values for new tuples (+ % d.e. opt.)
                    combs = reshape(
                        collect(Iterators.product((getdomain(a) for p ∈ cB0.domain)...)),
                        (1,:)
                    )
                    ncombs = length(combs)
                    Threads.@threads for ltzcombs ∈ shuffle(combs)[1:floor(Int, ncombs*diamondexpansion)]
                        for gtzcombs ∈ shuffle(combs)[1:floor(Int, ncombs*diamondexpansion)]
                            for eqzcombs ∈ shuffle(combs)[1:floor(Int, ncombs*diamondexpansion)]
                                # Must initialize at every (parallel) cycle!
                                # cB1 = o(cB) ∪ {z}
                                z = Point(Char(Int(last(cB0.domain).label)+1))
                                cB1 = AFSLOS(
                                    vcat(cB0.domain, z),
                                    cB0.algebra,
                                    Dict(cB0.mvlt),
                                    Dict(cB0.mveq)
                                )
                                cB1.mvlt[(z,z)] = ⊥
                                cB1.mveq[(z,z)] = ⊤

                                # cB2 = cB1 ∪ {t} = o(cB) ∪ {z,t}
                                t = Point(Char(Int(last(cB1.domain).label)+1))

                                for i ∈ 1:length(cB0.domain)
                                    cB1.mvlt[(cB0.domain[i],z)] = ltzcombs[i]
                                    cB1.mvlt[(z,cB0.domain[i])] = gtzcombs[i]
                                    cB1.mveq[(cB0.domain[i],z)] = eqzcombs[i]
                                    cB1.mveq[(z,cB0.domain[i])] = eqzcombs[i]
                                end
                                try
                                    checkafslos(cB1)
                                    # in general, < is not commutative!
                                    for zi ∈ cB0.domain
                                        isbot(cB1.mvlt[(zi,z)]) && continue # <(zi,z) ≻ 0
                                        βi = mveval(r, (x,y), (zi,z), cB1)
                                        if !isbot(βi) && precedeq(a, a.implication(βi, β), β)
                                            Threads.lock(u) do
                                                tj = HybridMVHSTableau{T}(
                                                    false,
                                                    (φ.children[1], a.implication(βi, β)),
                                                    Interval(zi,z),
                                                    cB1,
                                                    l
                                                )
                                                push!(metricheaps, tj)
                                            end
                                        end
                                    end
                                    for ti ∈ cB0.domain
                                        isbot(cB1.mvlt[(z,ti)]) && continue # <(z,ti) ≻ 0
                                        βi = mveval(r, (x,y), (z,ti), cB1)
                                        if !isbot(βi) && precedeq(a, a.implication(βi, β), β)
                                            Threads.lock(u) do
                                                tj = HybridMVHSTableau{T}(
                                                    false,
                                                    (φ.children[1], a.implication(βi, β)),
                                                    Interval(z,ti),
                                                    cB1,
                                                    l
                                                )
                                                push!(metricheaps, tj)
                                            end
                                        end
                                    end

                                    # cB2 = cB1 ∪ {t} = o(cB) ∪ {z,t}
                                    cB2 = AFSLOS(
                                        vcat(cB1.domain, t),
                                        cB1.algebra,
                                        Dict(cB1.mvlt),
                                        Dict(cB1.mveq)
                                    )
                                    cB2.mvlt[(t,t)] = ⊥
                                    cB2.mveq[(t,t)] = ⊤

                                    # All possible combinations of values for new tuples
                                    for lttcombs ∈ reshape(
                                        collect(Iterators.product((getdomain(a) for p ∈ cB1.domain)...)),
                                        (1,:)
                                    )
                                        for gttcombs ∈ reshape(
                                            collect(Iterators.product((getdomain(a) for p ∈ cB1.domain)...)),
                                            (1,:)
                                        )
                                            for eqtcombs ∈ reshape(
                                                collect(Iterators.product((getdomain(a) for p ∈ cB1.domain)...)),
                                                (1,:)
                                            )
                                                for i ∈ 1:length(cB1.domain)
                                                    cB2.mvlt[(cB1.domain[i],t)] = lttcombs[i]
                                                    cB2.mvlt[(t,cB1.domain[i])] = gttcombs[i]
                                                    cB2.mveq[(cB1.domain[i],t)] = eqtcombs[i]
                                                    cB2.mveq[(t,cB1.domain[i])] = eqtcombs[i]
                                                end
                                                isbot(cB2.mvlt[(z,t)]) && isbot(cB2.mvlt[(t,z)]) && continue
                                                try
                                                    checkafslos(cB2)
                                                    # in general, < is not commutative!
                                                    if !isbot(cB2.mvlt[(z,t)])  # <(z,t) ≻ 0
                                                        βi = mveval(r, (x,y), (z,t), cB2)
                                                        if !isbot(βi) && precedeq(a, a.implication(βi, β), β)
                                                            Threads.lock(u) do
                                                                tj = HybridMVHSTableau{T}(
                                                                    false,
                                                                    (φ.children[1], a.implication(βi, β)),
                                                                    Interval(z,t),
                                                                    cB2,
                                                                    l
                                                                )
                                                                push!(metricheaps, tj)
                                                            end
                                                        end
                                                    else    # <(t,z) ≻ 0
                                                        βi = mveval(r, (x,y), (t,z), cB2)
                                                        if !isbot(βi) && precedeq(a, a.implication(βi, β), β)
                                                            Threads.lock(u) do
                                                                tj = HybridMVHSTableau{T}(
                                                                    false,
                                                                    (φ.children[1], a.implication(βi, β)),
                                                                    Interval(t,z),
                                                                    cB2,
                                                                    l
                                                                )
                                                                push!(metricheaps, tj)
                                                            end
                                                        end
                                                    end
                                                catch err2
                                                    verbose && println(sprint(showerror, err2))
                                                end
                                            end
                                        end
                                    end
                                catch err1
                                    verbose && println(sprint(showerror, err1))
                                end
                            end
                        end
                    end
                end
            elseif en.judgement && !istop(β)
                # T⪯
                verbose && println("T⪯")
                for l ∈ findleaves(en)
                    ti = l
                    newnodes = false
                    for γ in minimalmembers(a, β)
                        if !findtableau(ti, false, (γ, φ), en.interval)
                            newnodes = true
                            ti = HybridMVHSTableau{T}(
                                false,
                                (γ, φ),
                                en.interval,
                                l.constraintsystem,
                                ti
                            )
                            push!(metricheaps, ti)
                        end
                    end
                    !newnodes && l == node && push!(metricheaps, node)
                end
            elseif !en.judgement && !istop(β)
                # F⪯
                verbose && println("F⪯")
                for l ∈ findleaves(en)
                    newnodes = false
                    for βi in minimalmembers(a, β)
                        newnodes = true
                        if !findtableau(l, true, (βi, φ), en.interval)
                            ti = HybridMVHSTableau{T}(
                                true,
                                (βi, φ),
                                en.interval,
                                l.constraintsystem,
                                l
                            )
                            push!(metricheaps, ti)
                        else  # Here there should be a branch and I need to keep track of it
                            ti = HybridMVHSTableau{T}(   # Fake node (always true)
                                true,
                                (⊤, ⊤),
                                en.interval,
                                l.constraintsystem,
                                l
                            )
                            push!(metricheaps, ti)
                        end
                    end
                    !newnodes && l == node && push!(metricheaps, node)
                end
            else
                # No condition matched, pushing node back into metricheaps
                push!(metricheaps, node)
            end
        end
        cycle+=1
    end
end

function hybridmvhsalphasat(
    metricheaps::Vector{MetricHeap},
    choosenode::Function,
    a::FiniteHeytingAlgebra{T,D},
    roots::Vector{HybridMVHSTableau};
    verbose::Bool=false,
    timeout::Union{Nothing,Int}=nothing,
    diamondexpansion::Float64=1.0
) where {
    T<:Truth,
    D<:AbstractVector{T}
}
    cycle = 0
    t0 = time_ns()
    while true
        
        if cycle%1e2==0
            cleanheaps!(metricheaps)
            # cleancss!(roots)
        end

        # if timeout, return false with a warning
        if !isnothing(timeout) && (time_ns()-t0)/1e9 > timeout
            verbose && println("Timeout")
            return nothing
        end

        # if using too much memory, try to free memory calling full GC sweep
        if cycle%10==0 && getfreemem() < gettotmem()*5e-2
            verbose && println("Calling Garbage Collector")
            GC.gc()
        end
        # if using too much memory, kill execution to avoid crashes
        if cycle%10==0 && getfreemem() < gettotmem()*5e-2
            verbose && println("Too much memory being used, exiting")
            return nothing
        end

        node = choosenode(metricheaps, cycle)
        isnothing(node) && return false # all branches are closed
        isexpanded(node) && return true # found a satisfiable branch
        en = findexpansionnode(node)
        expand!(en)
        verbose && println("expansion node:")
        verbose && println(en)
        if en.boundingimplication isa Tuple{Truth, Truth}
            β = en.boundingimplication[1]
            γ = en.boundingimplication[2]
            if en.judgement && !precedeq(a, β, γ)
                # X1
                verbose && println("X1")
                close!(en)
            elseif !en.judgement && precedeq(a, β, γ)
                # X2
                verbose && println("X2")
                close!(en)
            elseif !en.judgement && isbot(β)
                # X3
                verbose && println("X3")
                close!(en)
            elseif !en.judgement && istop(γ)
                # X4
                verbose && println("X4")
                close!(en)
            elseif findsimilar(en, a)
                # X5
                verbose && println("X5")
                close!(en)
            else
                # let err
                #     try
                #         checkafslos(en.constraintsystem)
                #     catch err
                #         # X6
                #         verbose && println(sprint(showerror, err))
                #         verbose && println("X6")
                #         close!(en)
                #     end
                # end
                # No condition matched, pushing node back into metricheaps
                push!(metricheaps, node)
            end
        elseif en.boundingimplication isa Tuple{Truth, Formula}
            β = en.boundingimplication[1]
            φ = en.boundingimplication[2]
            if !en.judgement && isbot(β)
                # X3
                verbose && println("X3")
                close!(en)                
            elseif findsimilar(en, a)
                # X5
                verbose && println("X5")
                close!(en)
            elseif en.judgement && token(φ) isa NamedConnective{:∧} && !isbot(β)
                # T∧
                verbose && println("T∧")
                for l ∈ findleaves(en)
                    t1 = HybridMVHSTableau{T}(
                        true,
                        (β, φ.children[1]),
                        en.interval,
                        l.constraintsystem,
                        l
                    )
                    push!(metricheaps, t1)
                    t2 = HybridMVHSTableau{T}(
                        true,
                        (β, φ.children[2]),
                        en.interval,
                        l.constraintsystem,
                        t1
                    )
                    push!(metricheaps, t2)
                end
            elseif !en.judgement && token(φ) isa NamedConnective{:∧} && !isbot(β)
                # F∧
                verbose && println("F∧")
                for l ∈ findleaves(en)
                    t1 = HybridMVHSTableau{T}(
                        false,
                        (β, φ.children[1]),
                        en.interval,
                        l.constraintsystem,
                        l
                    )
                    push!(metricheaps, t1)
                    t2 = HybridMVHSTableau{T}(
                        false,
                        (β, φ.children[2]),
                        en.interval,
                        l.constraintsystem,
                        l
                    )
                    push!(metricheaps, t2)
                end
            elseif en.judgement && token(φ) isa NamedConnective{:→} && !isbot(β)
                # T→
                verbose && println("T→")
                for γ ∈ lesservalues(a, β)
                    isbot(γ) && continue
                    for l ∈ findleaves(en)
                        t1 = HybridMVHSTableau{T}(
                            false,
                            (γ, φ.children[1]),
                            en.interval,
                            l.constraintsystem,
                            l
                        )
                        push!(metricheaps, t1)
                        t2 = HybridMVHSTableau{T}(
                            true,
                            (γ, φ.children[2]),
                            en.interval,
                            l.constraintsystem,
                            l
                        )
                        push!(metricheaps, t2)
                    end
                end
            elseif !en.judgement && token(φ) isa NamedConnective{:→} && !isbot(β)
                # F→
                verbose && println("F→")
                for l ∈ findleaves(en)
                    for βi ∈ lesservalues(a, β)
                        isbot(βi) && continue
                        t1 = HybridMVHSTableau{T}(
                            true,
                            (βi, φ.children[1]),
                            en.interval,
                            l.constraintsystem,
                            l
                        )
                        push!(metricheaps, t1)
                        t2 = HybridMVHSTableau{T}(
                            false,
                            (βi, φ.children[2]),
                            en.interval,
                            l.constraintsystem,
                            t1
                        )
                        push!(metricheaps, t2)
                    end
                end
            elseif en.judgement && token(φ) isa BoxRelationalConnective
                # T□"
                verbose && println("T□")
                for l ∈ findleaves(en)
                    r = SoleLogics.relation(token(φ))
                    (x, y) = (en.interval.x, en.interval.y)
                    cB = l.constraintsystem
                    tj = l
                    for zi ∈ cB.domain
                        for ti ∈ cB.domain
                            isbot(cB.mvlt[(zi,ti)]) && continue # <(zi,ti) ≻ 0
                            βi = mveval(r, (x,y), (zi,ti), cB)
                            if !isbot(βi) && precedeq(a, β, a.meet(β, βi))
                                # Optimization 1 (int. node)
                                if !findtableau(tj,true,(a.meet(β, βi), φ.children[1]),Interval(zi,ti))
                                    tj = HybridMVHSTableau{T}(
                                        true,
                                        (a.meet(β, βi), φ.children[1]),
                                        Interval(zi,ti),
                                        cB,
                                        tj
                                    )
                                    push!(metricheaps, tj)
                                end                                
                            end
                        end
                    end
                    # Optimization 2 (leaf node)
                    if en == l == tj
                        verbose && printsolution(en)
                        return true # found satisfiable branch
                    else
                        tj = HybridMVHSTableau{T}(
                            true,
                            (β, φ),
                            en.interval,
                            cB,
                            tj
                        )
                        push!(metricheaps, tj)
                    end
                end
            elseif !en.judgement && token(φ) isa BoxRelationalConnective
                # F□"
                verbose && println("F□")
                for l ∈ findleaves(en)
                    r = SoleLogics.relation(token(φ))
                    (x, y) = (en.interval.x, en.interval.y)
                    cB0 = l.constraintsystem

                    # cB0 = o(cB)
                    for zi ∈ cB0.domain
                        for ti ∈ cB0.domain
                            isbot(cB0.mvlt[(zi,ti)]) && continue # <(zi,ti) ≻ 0
                            βi = mveval(r, (x,y), (zi,ti), cB0)
                            if !isbot(βi) && precedeq(a, β, a.meet(β, βi))
                                tj = HybridMVHSTableau{T}(
                                    false,
                                    (a.meet(βi, β), φ.children[1]),
                                    Interval(zi,ti),
                                    cB0,
                                    l
                                )
                                push!(metricheaps, tj)
                            end
                        end
                    end

                    u = Threads.SpinLock();

                    # All possible combinations of values for new tuples (+ % d.e. opt.)
                    combs = reshape(
                        collect(Iterators.product((getdomain(a) for p ∈ cB0.domain)...)),
                        (1,:)
                    )
                    ncombs = length(combs)
                    Threads.@threads for ltzcombs ∈ shuffle(combs)[1:floor(Int, ncombs*diamondexpansion)]
                        for gtzcombs ∈ shuffle(combs)[1:floor(Int, ncombs*diamondexpansion)]
                            for eqzcombs ∈ shuffle(combs)[1:floor(Int, ncombs*diamondexpansion)]
                                # Must initialize at every (parallel) cycle!
                                # cB1 = o(cB) ∪ {z}
                                z = Point(Char(Int(last(cB0.domain).label)+1))
                                cB1 = AFSLOS(
                                    vcat(cB0.domain, z),
                                    cB0.algebra,
                                    Dict(cB0.mvlt),
                                    Dict(cB0.mveq)
                                )
                                cB1.mvlt[(z,z)] = ⊥
                                cB1.mveq[(z,z)] = ⊤
            
                                # cB2 = cB1 ∪ {t} = o(cB) ∪ {z,t}
                                t = Point(Char(Int(last(cB1.domain).label)+1))

                                for i ∈ 1:length(cB0.domain)
                                    cB1.mvlt[(cB0.domain[i],z)] = ltzcombs[i]
                                    cB1.mvlt[(z,cB0.domain[i])] = gtzcombs[i]
                                    cB1.mveq[(cB0.domain[i],z)] = eqzcombs[i]
                                    cB1.mveq[(z,cB0.domain[i])] = eqzcombs[i]
                                end
                                try
                                    checkafslos(cB1)
                                    # in general, < is not commutative!
                                    for zi ∈ cB0.domain
                                        isbot(cB1.mvlt[(zi,z)]) && continue # <(zi,z) ≻ 0
                                        βi = mveval(r, (x,y), (zi,z), cB1)
                                        if !isbot(βi) && precedeq(a, β, a.meet(β, βi))
                                            Threads.lock(u) do
                                                tj = HybridMVHSTableau{T}(
                                                    false,
                                                    (a.meet(βi, β), φ.children[1]),
                                                    Interval(zi,z),
                                                    cB1,
                                                    l
                                                )
                                                push!(metricheaps, tj)
                                            end
                                        end
                                    end
                                    for ti ∈ cB0.domain
                                        isbot(cB1.mvlt[(z,ti)]) && continue # <(z,ti) ≻ 0
                                        βi = mveval(r, (x,y), (z,ti), cB1)
                                        if !isbot(βi) && precedeq(a, β, a.meet(β, βi))
                                            Threads.lock(u) do
                                                tj = HybridMVHSTableau{T}(
                                                    false,
                                                    (a.meet(βi, β), φ.children[1]),
                                                    Interval(z,ti),
                                                    cB1,
                                                    l
                                                )
                                                push!(metricheaps, tj)
                                            end
                                        end
                                    end

                                    # cB2 = cB1 ∪ {t} = o(cB) ∪ {z,t}
                                    cB2 = AFSLOS(
                                        vcat(cB1.domain, t),
                                        cB1.algebra,
                                        Dict(cB1.mvlt),
                                        Dict(cB1.mveq)
                                    )
                                    cB2.mvlt[(t,t)] = ⊥
                                    cB2.mveq[(t,t)] = ⊤

                                    # All possible combinations of values for new tuples
                                    for lttcombs ∈ reshape(
                                        collect(Iterators.product((getdomain(a) for p ∈ cB1.domain)...)),
                                        (1,:)
                                    )
                                        for gttcombs ∈ reshape(
                                            collect(Iterators.product((getdomain(a) for p ∈ cB1.domain)...)),
                                            (1,:)
                                        )
                                            for eqtcombs ∈ reshape(
                                                collect(Iterators.product((getdomain(a) for p ∈ cB1.domain)...)),
                                                (1,:)
                                            )
                                                for i ∈ 1:length(cB1.domain)
                                                    cB2.mvlt[(cB1.domain[i],t)] = lttcombs[i]
                                                    cB2.mvlt[(t,cB1.domain[i])] = gttcombs[i]
                                                    cB2.mveq[(cB1.domain[i],t)] = eqtcombs[i]
                                                    cB2.mveq[(t,cB1.domain[i])] = eqtcombs[i]
                                                end
                                                isbot(cB2.mvlt[(z,t)]) && isbot(cB2.mvlt[(t,z)]) && continue
                                                try
                                                    checkafslos(cB2)
                                                    # in general, < is not commutative!
                                                    if !isbot(cB2.mvlt[(z,t)])  # <(z,t) ≻ 0
                                                        βi = mveval(r, (x,y), (z,t), cB2)
                                                        if !isbot(βi) && precedeq(a, β, a.meet(β, βi))
                                                            Threads.lock(u) do
                                                                tj = HybridMVHSTableau{T}(
                                                                    false,
                                                                    (a.meet(βi, β), φ.children[1]),
                                                                    Interval(z,t),
                                                                    cB2,
                                                                    l
                                                                )
                                                                push!(metricheaps, tj)
                                                            end
                                                        end
                                                    else    # <(t,z) ≻ 0
                                                        βi = mveval(r, (x,y), (t,z), cB2)
                                                        if !isbot(βi) && precedeq(a, β, a.meet(β, βi))
                                                            Threads.lock(u) do
                                                                tj = HybridMVHSTableau{T}(
                                                                    false,
                                                                    (a.meet(βi, β), φ.children[1]),
                                                                    Interval(t,z),
                                                                    cB2,
                                                                    l
                                                                )
                                                                push!(metricheaps, tj)
                                                            end
                                                        end
                                                    end
                                                catch err2
                                                    verbose && println(sprint(showerror, err2))
                                                end
                                            end
                                        end
                                    end
                                catch err1
                                    verbose && println(sprint(showerror, err1))
                                end
                            end
                        end
                    end
                end
            elseif en.judgement && !isbot(β)
                # T⪰
                verbose && println("T⪰")
                for l ∈ findleaves(en)
                    ti = l
                    newnodes = false
                    for γ in maximalmembers(a, β)
                        if !findtableau(ti, false, (φ, γ), en.interval)
                            newnodes = true
                            ti = HybridMVHSTableau{T}(
                                false,
                                (φ, γ),
                                en.interval,
                                l.constraintsystem,
                                ti
                            )
                            push!(metricheaps, ti)
                        end
                    end
                    !newnodes && l == node && push!(metricheaps, node)
                end
            elseif !en.judgement && !isbot(β)
                # F⪰
                verbose && println("F⪰")
                for l ∈ findleaves(en)
                    newnodes = false
                    for βi in maximalmembers(a, β)
                        newnodes = true
                        if !findtableau(l, true, (φ, βi), en.interval)
                            ti = HybridMVHSTableau{T}(
                                true,
                                (φ, βi),
                                en.interval,
                                l.constraintsystem,
                                l
                            )
                            push!(metricheaps, ti)
                        else  # Here there should be a branch and I need to keep track of it
                            ti = HybridMVHSTableau{T}(   # Fake node (always true)
                                true,
                                (⊤, ⊤),
                                en.interval,
                                l.constraintsystem,
                                l
                            )
                            push!(metricheaps, ti)
                        end
                    end
                    !newnodes && l == node && push!(metricheaps, node)
                end
            else
                # No condition matched, pushing node back into metricheaps
                push!(metricheaps, node)
            end
        elseif en.boundingimplication isa Tuple{Formula, Truth}
            φ = en.boundingimplication[1]
            β = en.boundingimplication[2]
            if !en.judgement && istop(β)
                # X4
                verbose && println("X4")
                close!(en)
            elseif en.judgement && token(φ) isa NamedConnective{:∨} && !istop(β)
                # T∨
                verbose && println("T∨")
                for l ∈ findleaves(en)
                    t1 = HybridMVHSTableau{T}(
                        true,
                        (φ.children[1], β),
                        en.interval,
                        l.constraintsystem,
                        l
                    )
                    push!(metricheaps, t1)
                    t2 = HybridMVHSTableau{T}(
                        true,
                        (φ.children[2], β),
                        en.interval,
                        l.constraintsystem,
                        t1
                    )
                    push!(metricheaps, t2)
                end
            elseif !en.judgement && token(φ) isa NamedConnective{:∨} && !istop(β)
                # F∨
                verbose && println("F∨")
                for l ∈ findleaves(en)
                    t1 = HybridMVHSTableau{T}(
                        false,
                        (φ.children[1], β),
                        en.interval,
                        l.constraintsystem,
                        l
                    )
                    push!(metricheaps, t1)
                    t2 = HybridMVHSTableau{T}(
                        false,
                        (φ.children[2], β),
                        en.interval,
                        l.constraintsystem,
                        l
                    )
                    push!(metricheaps, t2)
                end
            elseif en.judgement && token(φ) isa DiamondRelationalConnective
                # T◊"
                verbose && println("T◊")
                for l ∈ findleaves(en)
                    r = SoleLogics.relation(token(φ))
                    (x, y) = (en.interval.x, en.interval.y)
                    cB = l.constraintsystem
                    tj = l
                    for zi ∈ cB.domain
                        for ti ∈ cB.domain
                            isbot(cB.mvlt[(zi,ti)]) && continue # <(zi,ti) ≻ 0
                            βi = mveval(r, (x,y), (zi,ti), cB)
                            if !isbot(βi) && precedeq(a, a.implication(βi, β), β)
                                # Optimization 1 (int. node)
                                if !findtableau(tj,true,(φ.children[1], a.implication(βi, β)),Interval(zi,ti))
                                    tj = HybridMVHSTableau{T}(
                                        true,
                                        (φ.children[1], a.implication(βi, β)),
                                        Interval(zi,ti),
                                        cB,
                                        tj
                                    )
                                    push!(metricheaps, tj)
                                end
                            end
                        end
                    end
                    # Optimization 2 (leaf node)
                    if en == l == tj
                        verbose && printsolution(en)
                        return true # found satisfiable branch
                    else
                        tj = HybridMVHSTableau{T}(
                            true,
                            (φ, β),
                            en.interval,
                            cB,
                            tj
                        )
                        push!(metricheaps, tj)
                    end
                end
            elseif !en.judgement && token(φ) isa DiamondRelationalConnective
                # F◊
                verbose && println("F◊")
                for l ∈ findleaves(en)
                    r = SoleLogics.relation(token(φ))
                    (x, y) = (en.interval.x, en.interval.y)
                    cB0 = l.constraintsystem

                    # cB0 = o(cB)
                    for zi ∈ cB0.domain
                        for ti ∈ cB0.domain
                            isbot(cB0.mvlt[(zi,ti)]) && continue # <(zi,ti) ≻ 0
                            βi = mveval(r, (x,y), (zi,ti), cB0)
                            if !isbot(βi) && precedeq(a, a.implication(βi, β), β)
                                tj = HybridMVHSTableau{T}(
                                    false,
                                    (φ.children[1], a.implication(βi, β)),
                                    Interval(zi,ti),
                                    cB0,
                                    l
                                )
                                push!(metricheaps, tj)
                            end
                        end
                    end

                    u = Threads.SpinLock();

                    # All possible combinations of values for new tuples (+ % d.e. opt.)
                    combs = reshape(
                        collect(Iterators.product((getdomain(a) for p ∈ cB0.domain)...)),
                        (1,:)
                    )
                    ncombs = length(combs)
                    Threads.@threads for ltzcombs ∈ shuffle(combs)[1:floor(Int, ncombs*diamondexpansion)]
                        for gtzcombs ∈ shuffle(combs)[1:floor(Int, ncombs*diamondexpansion)]
                            for eqzcombs ∈ shuffle(combs)[1:floor(Int, ncombs*diamondexpansion)]
                                # Must initialize at every (parallel) cycle!
                                # cB1 = o(cB) ∪ {z}
                                z = Point(Char(Int(last(cB0.domain).label)+1))
                                cB1 = AFSLOS(
                                    vcat(cB0.domain, z),
                                    cB0.algebra,
                                    Dict(cB0.mvlt),
                                    Dict(cB0.mveq)
                                )
                                cB1.mvlt[(z,z)] = ⊥
                                cB1.mveq[(z,z)] = ⊤

                                # cB2 = cB1 ∪ {t} = o(cB) ∪ {z,t}
                                t = Point(Char(Int(last(cB1.domain).label)+1))

                                for i ∈ 1:length(cB0.domain)
                                    cB1.mvlt[(cB0.domain[i],z)] = ltzcombs[i]
                                    cB1.mvlt[(z,cB0.domain[i])] = gtzcombs[i]
                                    cB1.mveq[(cB0.domain[i],z)] = eqzcombs[i]
                                    cB1.mveq[(z,cB0.domain[i])] = eqzcombs[i]
                                end
                                try
                                    checkafslos(cB1)
                                    # in general, < is not commutative!
                                    for zi ∈ cB0.domain
                                        isbot(cB1.mvlt[(zi,z)]) && continue # <(zi,z) ≻ 0
                                        βi = mveval(r, (x,y), (zi,z), cB1)
                                        if !isbot(βi) && precedeq(a, a.implication(βi, β), β)
                                            Threads.lock(u) do
                                                tj = HybridMVHSTableau{T}(
                                                    false,
                                                    (φ.children[1], a.implication(βi, β)),
                                                    Interval(zi,z),
                                                    cB1,
                                                    l
                                                )
                                                push!(metricheaps, tj)
                                            end
                                        end
                                    end
                                    for ti ∈ cB0.domain
                                        isbot(cB1.mvlt[(z,ti)]) && continue # <(z,ti) ≻ 0
                                        βi = mveval(r, (x,y), (z,ti), cB1)
                                        if !isbot(βi) && precedeq(a, a.implication(βi, β), β)
                                            Threads.lock(u) do
                                                tj = HybridMVHSTableau{T}(
                                                    false,
                                                    (φ.children[1], a.implication(βi, β)),
                                                    Interval(z,ti),
                                                    cB1,
                                                    l
                                                )
                                                push!(metricheaps, tj)
                                            end
                                        end
                                    end

                                    # cB2 = cB1 ∪ {t} = o(cB) ∪ {z,t}
                                    cB2 = AFSLOS(
                                        vcat(cB1.domain, t),
                                        cB1.algebra,
                                        Dict(cB1.mvlt),
                                        Dict(cB1.mveq)
                                    )
                                    cB2.mvlt[(t,t)] = ⊥
                                    cB2.mveq[(t,t)] = ⊤

                                    # All possible combinations of values for new tuples
                                    for lttcombs ∈ reshape(
                                        collect(Iterators.product((getdomain(a) for p ∈ cB1.domain)...)),
                                        (1,:)
                                    )
                                        for gttcombs ∈ reshape(
                                            collect(Iterators.product((getdomain(a) for p ∈ cB1.domain)...)),
                                            (1,:)
                                        )
                                            for eqtcombs ∈ reshape(
                                                collect(Iterators.product((getdomain(a) for p ∈ cB1.domain)...)),
                                                (1,:)
                                            )
                                                for i ∈ 1:length(cB1.domain)
                                                    cB2.mvlt[(cB1.domain[i],t)] = lttcombs[i]
                                                    cB2.mvlt[(t,cB1.domain[i])] = gttcombs[i]
                                                    cB2.mveq[(cB1.domain[i],t)] = eqtcombs[i]
                                                    cB2.mveq[(t,cB1.domain[i])] = eqtcombs[i]
                                                end
                                                isbot(cB2.mvlt[(z,t)]) && isbot(cB2.mvlt[(t,z)]) && continue
                                                try
                                                    checkafslos(cB2)
                                                    # in general, < is not commutative!
                                                    if !isbot(cB2.mvlt[(z,t)])  # <(z,t) ≻ 0
                                                        βi = mveval(r, (x,y), (z,t), cB2)
                                                        if !isbot(βi) && precedeq(a, a.implication(βi, β), β)
                                                            Threads.lock(u) do
                                                                tj = HybridMVHSTableau{T}(
                                                                    false,
                                                                    (φ.children[1], a.implication(βi, β)),
                                                                    Interval(z,t),
                                                                    cB2,
                                                                    l
                                                                )
                                                                push!(metricheaps, tj)
                                                            end
                                                        end
                                                    else    # <(t,z) ≻ 0
                                                        βi = mveval(r, (x,y), (t,z), cB2)
                                                        if !isbot(βi) && precedeq(a, a.implication(βi, β), β)
                                                            Threads.lock(u) do
                                                                tj = HybridMVHSTableau{T}(
                                                                    false,
                                                                    (φ.children[1], a.implication(βi, β)),
                                                                    Interval(t,z),
                                                                    cB2,
                                                                    l
                                                                )
                                                                push!(metricheaps, tj)
                                                            end
                                                        end
                                                    end
                                                catch err2
                                                    verbose && println(sprint(showerror, err2))
                                                end
                                            end
                                        end
                                    end
                                catch err1
                                    verbose && println(sprint(showerror, err1))
                                end
                            end
                        end
                    end
                end
            elseif en.judgement && !istop(β)
                # T⪯
                verbose && println("T⪯")
                for l ∈ findleaves(en)
                    ti = l
                    newnodes = false
                    for γ in minimalmembers(a, β)
                        if !findtableau(ti, false, (γ, φ), en.interval)
                            newnodes = true
                            ti = HybridMVHSTableau{T}(
                                false,
                                (γ, φ),
                                en.interval,
                                l.constraintsystem,
                                ti
                            )
                            push!(metricheaps, ti)
                        end
                    end
                    !newnodes && l == node && push!(metricheaps, node)
                end
            elseif !en.judgement && !istop(β)
                # F⪯
                verbose && println("F⪯")
                for l ∈ findleaves(en)
                    newnodes = false
                    for βi in minimalmembers(a, β)
                        newnodes = true
                        if !findtableau(l, true, (βi, φ), en.interval)
                            ti = HybridMVHSTableau{T}(
                                true,
                                (βi, φ),
                                en.interval,
                                l.constraintsystem,
                                l
                            )
                            push!(metricheaps, ti)
                        else  # Here there should be a branch and I need to keep track of it
                            ti = HybridMVHSTableau{T}(   # Fake node (always true)
                                true,
                                (⊤, ⊤),
                                en.interval,
                                l.constraintsystem,
                                l
                            )
                            push!(metricheaps, ti)
                        end
                    end
                    !newnodes && l == node && push!(metricheaps, node)
                end
            else
                # No condition matched, pushing node back into metricheaps
                push!(metricheaps, node)
            end
        end
        cycle+=1
    end
end

function hybridmvhsalphasat(
    α::T1,
    φ::Formula,
    a::A,
    choosenode::Function,
    metrics::Function...;
    verbose::Bool=false,
    timeout::Union{Nothing,Int}=nothing,
    diamondexpansion::Float64=1.0
) where {
    T<:Truth,
    D<:AbstractVector{T},
    A<:FiniteAlgebra{T,D},
    T1<:Truth
}
    if diamondexpansion < 0.0 || diamondexpansion > 1.0
        error("% diamond expansion must be between 0.0 and 1.0")
    end
    if !isa(α, T) α = convert(T, α) end
    tableaux = Vector{HybridMVHSTableau}()
    x, y = Point.(['A', 'B'])
    for δ ∈ getdomain(a)
        istop(δ) && continue    # (1)
        for β ∈ getdomain(a)
            isbot(β) && continue    # <(x,y) ≻ 0
            for γ ∈ getdomain(a)
                afslos = AFSLOS(
                    [x, y],
                    a,
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
                        HybridMVHSTableau{T}(
                            true,
                            (α, φ),
                            Interval(x, y),
                            afslos
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
    r = hybridmvhsalphasat(metricheaps, choosenode, a, tableaux; verbose, timeout, diamondexpansion)
    if isnothing(r) || r || diamondexpansion == 1.0
        return r
    else
        @warn "WARNING: α-sat returned false with % diamond expansion set to $diamondexpansion"
        return r
    end
end

function hybridmvhsalphasat(
    α::T1,
    φ::Formula,
    a::A,
    metric::Function;
    verbose::Bool=false,
    timeout::Union{Nothing,Int}=nothing,
    diamondexpansion::Float64=1.0
) where {
    T<:Truth,
    D<:AbstractVector{T},
    A<:FiniteAlgebra{T,D},
    T1<:Truth
}
    hybridmvhsalphasat(α, φ, a, roundrobin, metric; verbose, timeout, diamondexpansion)
end

function hybridmvhsalphasat(
    α::T1,
    φ::Formula,
    a::A;
    rng = Random.GLOBAL_RNG,
    verbose::Bool=false,
    timeout::Union{Nothing,Int}=nothing,
    diamondexpansion::Float64=1.0
) where {
    T<:Truth,
    D<:AbstractVector{T},
    A<:FiniteAlgebra{T,D},
    T1<:Truth
}
    randombranch(_::HybridMVHSTableau) = rand(rng, Int)
    hybridmvhsalphasat(α, φ, a, randombranch; verbose, timeout, diamondexpansion)
end

function hybridmvhsalphaprove(
    α::T1,
    φ::Formula,
    a::A,
    choosenode::Function,
    metrics::Function...;
    verbose::Bool=false,
    timeout::Union{Nothing,Int}=nothing,
    diamondexpansion::Float64=1.0
) where {
    T<:Truth,
    D<:AbstractVector{T},
    A<:FiniteAlgebra{T,D},
    T1<:Truth
}
    if diamondexpansion < 0.0 || diamondexpansion > 1.0
        error("% diamond expansion must be between 0.0 and 1.0")
    end
    if !isa(α, T) α = convert(T, α) end
    tableaux = Vector{HybridMVHSTableau}()
    x, y = Point.(['A', 'B'])
    for δ ∈ getdomain(a)
        istop(δ) && continue    # (1)
        for β ∈ getdomain(a)
            isbot(β) && continue    # <(x,y) ≻ 0
            for γ ∈ getdomain(a)
                afslos = AFSLOS(
                    [x, y],
                    a,
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
                        HybridMVHSTableau{T}(
                            false,
                            (α, φ),
                            Interval(x, y),
                            afslos
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
    r = hybridmvhsalphasat(metricheaps, choosenode, a, tableaux; verbose, timeout, diamondexpansion)
    if isnothing(r)
        return r
    elseif !r || diamondexpansion == 1.0
        return !r
    else
        @warn "WARNING: α-val returned true with % diamond expansion set to $diamondexpansion"
        return !r
    end
end

function hybridmvhsalphaprove(
    α::T1,
    φ::Formula,
    a::A,
    metric::Function;
    verbose::Bool=false,
    timeout::Union{Nothing,Int}=nothing,
    diamondexpansion::Float64=1.0
) where {
    T<:Truth,
    D<:AbstractVector{T},
    A<:FiniteAlgebra{T,D},
    T1<:Truth
}
    hybridmvhsalphaprove(α, φ, a, roundrobin, metric; verbose, timeout, diamondexpansion)
end

function hybridmvhsalphaprove(
    α::T1,
    φ::Formula,
    a::A;
    rng = Random.GLOBAL_RNG,
    verbose::Bool=false,
    timeout::Union{Nothing,Int}=nothing,
    diamondexpansion::Float64=1.0
) where {
    T<:Truth,
    D<:AbstractVector{T},
    A<:FiniteAlgebra{T,D},
    T1<:Truth
}
    randombranch(_::HybridMVHSTableau) = rand(rng, Int)
    hybridmvhsalphaprove(α, φ, a, randombranch; verbose, timeout, diamondexpansion)
end
