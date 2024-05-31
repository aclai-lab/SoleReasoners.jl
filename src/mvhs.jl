struct Point
    label::Char
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

"""
The natural definition of many-valued Allen's relations. 
For every X ∈ {A, Ai, L, Li, B, Bi, E, Ei, D, Di, O, Oi} we have RX: I(D)×I(D)→H defined by:

 - RA([x,y],[z,t]) = =(y,z)
 - RL([x,y],[z,t]) = <(y,z)
 - RB([x,y],[z,t]) = =(x,z) ∩ <(t,y)
 - RE([x,y],[z,t]) = <(x,z) ∩ =(y,t)
 - RD([x,y],[z,t]) = <(x,z) ∩ <(t,y)
 - RO([x,y],[z,t]) = <(x,z) ∩ <(z,y) ∩ <(y,t)

and similarly for the inverse relations:

- RAi([x,y],[z,t]) = =(t,x)
- RLi([x,y],[z,t]) = <(t,x)
- RBi([x,y],[z,t]) = =(z,x) ∩ <(y,t)
- REi([x,y],[z,t]) = <(z,x) ∩ =(t,y)
- RDi([x,y],[z,t]) = <(z,x) ∩ <(y,t)
- ROi([x,y],[z,t]) = <(z,x) ∩ <(x,t) ∩ <(y,t)
"""
function mveval(
    r::R,
    (x,y)::Tuple{Point,Point},
    (z,t)::Tuple{Point,Point},
    c::AFSLOS
) where {
    R<:AbstractRelation
}
    if r == SoleLogics.IA_A
        return c.mveq[(y,z)]
    elseif r == SoleLogics.IA_L
        return c.mvlt[(y,z)]
    elseif r == SoleLogics.IA_B
        return c.algebra.meet(c.mveq[(x,z)], c.mvlt(t,y))
    elseif r == SoleLogics.IA_E
        return c.algebra.meet(c.mvlt[(x,z)], c.mveq(y,t))
    elseif r == SoleLogics.IA_D
        return c.algebra.meet(c.mvlt[(x,z)], c.mvlt(t,y))
    elseif r == SoleLogics.IA_O
        return c.algebra.meet(c.algebra.meet(c.mvlt[(x,z)], c.mvlt(z,y)), c.mvlt[(y,t)])
    elseif r == SoleLogics.IA_A
        return c.mveq[(t,x)]
    elseif r == SoleLogics.IA_L
        return c.mvlt[(t,x)]
    elseif r == SoleLogics.IA_B
        return c.algebra.meet(c.mveq[(z,x)], c.mvlt(y,t))
    elseif r == SoleLogics.IA_E
        return c.algebra.meet(c.mvlt[(z,x)], c.mveq(t,y))
    elseif r == SoleLogics.IA_D
        return c.algebra.meet(c.mvlt[(z,x)], c.mvlt(y,t))
    elseif r == SoleLogics.IA_O
        return c.algebra.meet(c.algebra.meet(c.mvlt[(z,x)], c.mvlt(x,t)), c.mvlt[(t,y)])
    else
        error("Relation $r not in HS")
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

    function MVHSTableau(
        judgement::Bool,
        boundingimplication::Union{
            Tuple{FiniteTruth,Formula},
            Tuple{Formula,FiniteTruth},
            Tuple{FiniteTruth,FiniteTruth}
        },
        interval::Interval,
        constraintsystem::AFSLOS
    )
        return new(
            judgement,
            boundingimplication,
            interval,
            constraintsystem,
            nothing,
            Vector{MVHSTableau}(),
            false,
            false
        )
    end

    function MVHSTableau(
        judgement::Bool,
        boundingimplication::Union{
            Tuple{FiniteTruth,Formula},
            Tuple{Formula,FiniteTruth},
            Tuple{FiniteTruth,FiniteTruth}
        },
        interval::Interval,
        constraintsystem::AFSLOS,
        father::MVHSTableau
    )
        t = new(
            judgement,
            boundingimplication,
            interval,
            constraintsystem,
            father,
            Vector{MVHSTableau}(),
            false,
            false
        )
        pushchildren!(father, t)
        return t
    end
end

isroot(t::MVHSTableau) = isnothing(t.father)
isleaf(t::MVHSTableau) = isempty(t.children)
isexpanded(t::MVHSTableau) = t.expanded
isclosed(t::MVHSTableau) = t.closed

expand!(t::MVHSTableau) = t.expanded = true

function close!(t::MVHSTableau)
    t.closed = true
    while !isempty(t.children)
        c = pop!(t.children)
        close!(c)
    end
end

function pushchildren!(t::MVHSTableau, children::MVHSTableau...)
    push!(t.children, children...)
end

function findexpansionnode(t::MVHSTableau)
    isroot(t) || isexpanded(t.father) ? t : findexpansionnode(t.father)
end

function findleaves(leavesset::Vector{MVHSTableau}, t::MVHSTableau)
    if isempty(t.children)
        push!(leavesset, t)
    else
        for child ∈ t.children
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
        "C = (\n\t<: $(t.constraintsystem.mvlt),\n\t=: $(t.constraintsystem.mveq)\n)"
    )
end

function findsimilar(
    t::MVHSTableau,
    a::A
) where {
    T<:Truth,
    D<:AbstractVector{T},
    A<:FiniteAlgebra{T,D}
}
    ψ = t.boundingimplication[2]
    if t.judgement
        β = t.boundingimplication[1]
        # Looking for F(α⪯ψ) where α⪯β
        while !isroot(t)
            t = t.father
            α = t.boundingimplication[1]
            if α isa Truth && t.boundingimplication[2] == ψ && !t.judgement && precedeq(a, α, β)
                return true
            end
        end
    else
        α = t.boundingimplication[1]
        # Looking for T(β⪯ψ) where α⪯β
        while !isroot(t)
            t = t.father
            β = t.boundingimplication[1]
            if β isa Truth && t.boundingimplication[2] == ψ && t.judgement && precedeq(a, α, β)
                return true
            end
        end
    end
    return false
end


function mvhsalphasat(
    metricheaps::Vector{MetricHeap},
    choosenode::Function,
    a::FiniteHeytingAlgebra;
    verbose::Bool=false
) 
    cycle = 0
    while true
        node = choosenode(metricheaps, cycle)
        isnothing(node) && return false # all branches are closed
        isexpanded(node) && return true # found a satisfiable branch
        en = findexpansionnode(node)
        expand!(en)
        verbose && println("expansion node:")
        verbose && println(en)
        if en.boundingimplication isa Tuple{Truth, Truth}
            α = en.boundingimplication[1]
            β = en.boundingimplication[2]
            if en.judgement && !precedeq(a, α, β)
                # X1
                verbose && println("X1")
                close!(en)
            elseif !en.judgement && precedeq(a, α, β)
                # X2
                verbose && println("X2")
                close!(en)
            elseif !en.judgement && isbot(α)
                # X3
                verbose && println("X3")
                close!(en)
            elseif !en.judgement && istop(β)
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
            α = en.boundingimplication[1]
            φ = en.boundingimplication[2]
            if !en.judgement && isbot(α)
                # X3
                verbose && println("X3")
                close!(en)                
            elseif findsimilar(en, a)
                # X5
                verbose && println("X5")
                close!(en)
            elseif en.judgement && token(φ) isa NamedConnective{:∧} && !isbot(α)
                # T∧
                verbose && println("T∧")
                for l ∈ findleaves(en)
                    verbose && println(l)
                    t1 = MVHSTableau(
                        true,
                        (α, φ.children[1]),
                        en.interval,
                        l.constraintsystem,
                        l
                    )
                    push!(metricheaps, t1)
                    verbose && println(t1)
                    t2 = MVHSTableau(
                        true,
                        (α, φ.children[2]),
                        en.interval,
                        l.constraintsystem,
                        t1
                    )
                    push!(metricheaps, t2)
                    verbose && println(t2)
                    verbose && println()
                end
            elseif !en.judgement && token(φ) isa NamedConnective{:∧} && !isbot(α)
                # F∧
                verbose && println("F∧")
                for l ∈ findleaves(en)
                    verbose && println(l)
                    t1 = MVHSTableau(
                        false,
                        (α, φ.children[1]),
                        en.interval,
                        l.constraintsystem,
                        l
                    )
                    push!(metricheaps, t1)
                    verbose && println(t1)
                    t2 = MVHSTableau(
                        false,
                        (α, φ.children[2]),
                        en.interval,
                        l.constraintsystem,
                        l
                    )
                    push!(metricheaps, t2)
                    verbose && println(t2)
                    verbose && println()
                end
            elseif en.judgement && token(φ) isa NamedConnective{:→} && !isbot(α)
                # T→
                verbose && println("T→")
                for γ ∈ lesservalues(a, α)
                    isbot(γ) && continue
                    for l ∈ findleaves(en)
                        t1 = MVHSTableau(
                            false,
                            (γ, φ.children[1]),
                            en.interval,
                            l.constraintsystem,
                            l
                        )
                        push!(metricheaps, t1)
                        verbose && println(t1)
                        t2 = MVHSTableau(
                            true,
                            (γ, φ.children[2]),
                            en.interval,
                            l.constraintsystem,
                            l
                        )
                        push!(metricheaps, t2)
                        verbose && println(t2)
                        verbose && println()
                    end
                end
            elseif !en.judgement && token(φ) isa NamedConnective{:→} && !isbot(α)
                # F→
                verbose && println("F→")
                for l ∈ findleaves(en)
                    for βi ∈ lesservalues(a, α)
                        isbot(βi) && continue
                        t1 = MVHSTableau(
                            true,
                            (βi, φ.children[1]),
                            en.interval,
                            l.constraintsystem,
                            l
                        )
                        push!(metricheaps, t1)
                        verbose && println(t1)
                        t2 = MVHSTableau(
                            false,
                            (βi, φ.children[2]),
                            en.interval,
                            l.constraintsystem,
                            t1
                        )
                        push!(metricheaps, t2)
                        verbose && println(t2)
                        verbose && println()
                    end
                end
            elseif en.judgement && token(φ) isa BoxRelationalConnective
                # T□"
                verbose && println("T□")
                for l ∈ findleaves(en)
                    verbose && println(l)
                    r = SoleLogics.relation(token(φ))
                    (x, y) = (en.interval.x, en.interval.y)
                    cB = l.constraintsystem
                    tj = l
                    for zi ∈ cB.domain
                        for ti ∈ cB.domain
                            isbot(cB.mvlt[(zi,ti)]) && continue # <(zi,ti) ≻ 0
                            βi = mveval(r, (x,y), (zi,ti), cB)
                            if !isbot(βi) && precedeq(a, α, a.meet(α, βi))
                                tj = MVHSTableau(
                                    true,
                                    (a.meet(α, βi), φ.children[1]),
                                    Interval(zi,ti),
                                    cB,
                                    tj
                                )
                                push!(metricheaps, tj)
                                verbose && println(tj)
                            end
                        end
                    end
                    tj = MVHSTableau(
                        true,
                        (α, φ),
                        en.interval,
                        cB,
                        tj
                    )
                    push!(metricheaps, tj)
                    verbose && println(tj)
                    verbose && println()
                end
            elseif !en.judgement && token(φ) isa BoxRelationalConnective
                # F□"
                verbose && println("F□")
                for l ∈ findleaves(en)
                    verbose && println(l)
                    r = SoleLogics.relation(token(φ))
                    (x, y) = (en.interval.x, en.interval.y)
                    cB0 = l.constraintsystem

                    # cB0 = o(cB)
                    for zi ∈ cB0.domain
                        for ti ∈ cB0.domain
                            isbot(cB0.mvlt[(zi,ti)]) && continue # <(zi,ti) ≻ 0
                            βi = mveval(r, (x,y), (zi,ti), cB0)
                            if !isbot(βi) && precedeq(a, α, a.meet(α, βi))
                                tj = MVHSTableau(
                                    false,
                                    (a.meet(βi, α), φ.children[1]),
                                    Interval(zi,ti),
                                    cB0,
                                    l
                                )
                                push!(metricheaps, tj)
                                verbose && println(tj)
                            end
                        end
                    end

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

                    # All possible combinations of values for new tuples
                    for ltzcombs ∈ reshape(
                        collect(Iterators.product((getdomain(a) for p ∈ cB0.domain)...)),
                        (1,:)
                    )
                        for gtzcombs ∈ reshape(
                            collect(Iterators.product((getdomain(a) for p ∈ cB0.domain)...)),
                            (1,:)
                        )
                            for eqzcombs ∈ reshape(
                                collect(Iterators.product((getdomain(a) for p ∈ cB0.domain)...)),
                                (1,:)
                            )
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
                                        if !isbot(βi) && precedeq(a, α, a.meet(α, βi))
                                            tj = MVHSTableau(
                                                false,
                                                (a.meet(βi, α), φ.children[1]),
                                                Interval(zi,z),
                                                cB1,
                                                l
                                            )
                                            push!(metricheaps, tj)
                                            verbose && println(tj)
                                        end
                                    end
                                    for ti ∈ cB0.domain
                                        isbot(cB1.mvlt[(z,ti)]) && continue # <(z,ti) ≻ 0
                                        βi = mveval(r, (x,y), (z,ti), cB1)
                                        if !isbot(βi) && precedeq(a, α, a.meet(α, βi))
                                            tj = MVHSTableau(
                                                false,
                                                (a.meet(βi, α), φ.children[1]),
                                                Interval(z,ti),
                                                cB1,
                                                l
                                            )
                                            push!(metricheaps, tj)
                                            verbose && println(tj)
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
                                                        if !isbot(βi) && precedeq(a, α, a.meet(α, βi))
                                                            tj = MVHSTableau(
                                                                false,
                                                                (a.meet(βi, α), φ.children[1]),
                                                                Interval(z,t),
                                                                cB2,
                                                                l
                                                            )
                                                            push!(metricheaps, tj)
                                                            verbose && println(tj)
                                                        end
                                                    else    # <(t,z) ≻ 0
                                                        βi = mveval(r, (x,y), (t,z), cB2)
                                                        if !isbot(βi) && precedeq(a, α, a.meet(α, βi))
                                                            tj = MVHSTableau(
                                                                false,
                                                                (a.meet(βi, α), φ.children[1]),
                                                                Interval(t,z),
                                                                cB2,
                                                                l
                                                            )
                                                            push!(metricheaps, tj)
                                                            verbose && println(tj)
                                                        end
                                                    end
                                                catch err2
                                                    #verbose && println(sprint(showerror, err2))
                                                end
                                            end
                                        end
                                    end
                                catch err1
                                    # verbose && println(sprint(showerror, err1))
                                    # return
                                end
                            end
                        end
                    end
                    verbose && println()
                end
            elseif en.judgement && !isbot(α)
                # T⪰
                verbose && println("T⪰")
                for l ∈ findleaves(en)
                    verbose && println(l)
                    ti = l
                    for γ in maximalmembers(a, α)
                        ti = MVHSTableau(
                            false,
                            (φ, γ),
                            en.interval,
                            l.constraintsystem,
                            ti
                        )
                        push!(metricheaps, ti)
                        verbose && println(ti)
                    end
                    verbose && println()
                end
            elseif !en.judgement && !isbot(α)
                # F⪰
                verbose && println("F⪰")
                for l ∈ findleaves(en)
                    verbose && println(l)
                    for βi in maximalmembers(a, α)
                        ti = MVHSTableau(
                            true,
                            (φ, βi),
                            en.interval,
                            l.constraintsystem,
                            l
                        )
                        push!(metricheaps, ti)
                        verbose && println(ti)
                    end
                    verbose && println()
                end
            else
                # No condition matched, pushing node back into metricheaps
                push!(metricheaps, node)
            end
        elseif en.boundingimplication isa Tuple{Formula, Truth}
            φ = en.boundingimplication[1]
            α = en.boundingimplication[2]
            if !en.judgement && istop(α)
                # X4
                verbose && println("X4")
                close!(en)
            elseif en.judgement && token(φ) isa NamedConnective{:∨} && !istop(α)
                # T∨
                verbose && println("T∨")
                for l ∈ findleaves(en)
                    verbose && println(l)
                    t1 = MVHSTableau(
                        true,
                        (φ.children[1], α),
                        en.interval,
                        l.constraintsystem,
                        l
                    )
                    push!(metricheaps, t1)
                    verbose && println(t1)
                    t2 = MVHSTableau(
                        true,
                        (φ.children[2], α),
                        en.interval,
                        l.constraintsystem,
                        t1
                    )
                    push!(metricheaps, t2)
                    verbose && println(t2)
                    verbose && println()
                end
            elseif !en.judgement && token(φ) isa NamedConnective{:∨} && !istop(α)
                # F∨
                verbose && println("F∨")
                for l ∈ findleaves(en)
                    verbose && println(l)
                    t1 = MVHSTableau(
                        false,
                        (φ.children[1], α),
                        en.interval,
                        l.constraintsystem,
                        l
                    )
                    push!(metricheaps, t1)
                    verbose && println(t1)
                    t2 = MVHSTableau(
                        false,
                        (φ.children[2], α),
                        en.interval,
                        l.constraintsystem,
                        l
                    )
                    push!(metricheaps, t2)
                    verbose && println(t2)
                    verbose && println()
                end
            elseif en.judgement && token(φ) isa DiamondRelationalConnective
                # T◊"
                verbose && println("T◊")
                for l ∈ findleaves(en)
                    verbose && println(l)
                    r = SoleLogics.relation(token(φ))
                    (x, y) = (en.interval.x, en.interval.y)
                    cB = l.constraintsystem
                    tj = l
                    for zi ∈ cB.domain
                        for ti ∈ cB.domain
                            isbot(cB.mvlt[(zi,ti)]) && continue # <(zi,ti) ≻ 0
                            βi = mveval(r, (x,y), (zi,ti), cB)
                            if !isbot(βi) && precedeq(a, a.implication(βi, α), α)
                                tj = MVHSTableau(
                                    true,
                                    (φ.children[1], a.implication(βi, α)),
                                    Interval(zi,ti),
                                    cB,
                                    tj
                                )
                                push!(metricheaps, tj)
                                verbose && println(tj)
                            end
                        end
                    end
                    tj = MVHSTableau(
                        true,
                        (φ, α),
                        en.interval,
                        cB,
                        tj
                    )
                    push!(metricheaps, tj)
                    verbose && println(tj)
                    verbose && println()
                end
            elseif !en.judgement && token(φ) isa DiamondRelationalConnective
                # F◊
                verbose && println("F◊")
                for l ∈ findleaves(en)
                    verbose && println(l)
                    r = SoleLogics.relation(token(φ))
                    (x, y) = (en.interval.x, en.interval.y)
                    cB0 = l.constraintsystem

                    # cB0 = o(cB)
                    for zi ∈ cB0.domain
                        for ti ∈ cB0.domain
                            isbot(cB0.mvlt[(zi,ti)]) && continue # <(zi,ti) ≻ 0
                            βi = mveval(r, (x,y), (zi,ti), cB0)
                            if !isbot(βi) && precedeq(a, a.implication(βi, α), α)
                                tj = MVHSTableau(
                                    false,
                                    (φ.children[1], a.implication(βi, α)),
                                    Interval(zi,ti),
                                    cB0,
                                    l
                                )
                                push!(metricheaps, tj)
                                verbose && println(tj)
                            end
                        end
                    end

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

                    # All possible combinations of values for new tuples
                    for ltzcombs ∈ reshape(
                        collect(Iterators.product((getdomain(a) for p ∈ cB0.domain)...)),
                        (1,:)
                    )
                        for gtzcombs ∈ reshape(
                            collect(Iterators.product((getdomain(a) for p ∈ cB0.domain)...)),
                            (1,:)
                        )
                            for eqzcombs ∈ reshape(
                                collect(Iterators.product((getdomain(a) for p ∈ cB0.domain)...)),
                                (1,:)
                            )
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
                                        if !isbot(βi) && precedeq(a, a.implication(βi, α), α)
                                            tj = MVHSTableau(
                                                false,
                                                (φ.children[1], a.implication(βi, α)),
                                                Interval(zi,z),
                                                cB1,
                                                l
                                            )
                                            push!(metricheaps, tj)
                                            verbose && println(tj)
                                        end
                                    end
                                    for ti ∈ cB0.domain
                                        isbot(cB1.mvlt[(z,ti)]) && continue # <(z,ti) ≻ 0
                                        βi = mveval(r, (x,y), (z,ti), cB1)
                                        if !isbot(βi) && precedeq(a, a.implication(βi, α), α)
                                            tj = MVHSTableau(
                                                false,
                                                (φ.children[1], a.implication(βi, α)),
                                                Interval(z,ti),
                                                cB1,
                                                l
                                            )
                                            push!(metricheaps, tj)
                                            verbose && println(tj)
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
                                                        if !isbot(βi) && precedeq(a, a.implication(βi, α), α)
                                                            tj = MVHSTableau(
                                                                false,
                                                                (φ.children[1], a.implication(βi, α)),
                                                                Interval(z,t),
                                                                cB2,
                                                                l
                                                            )
                                                            push!(metricheaps, tj)
                                                            verbose && println(tj)
                                                        end
                                                    else    # <(t,z) ≻ 0
                                                        βi = mveval(r, (x,y), (t,z), cB2)
                                                        if !isbot(βi) && precedeq(a, a.implication(βi, α), α)
                                                            tj = MVHSTableau(
                                                                false,
                                                                (φ.children[1], a.implication(βi, α)),
                                                                Interval(t,z),
                                                                cB2,
                                                                l
                                                            )
                                                            push!(metricheaps, tj)
                                                            verbose && println(tj)
                                                        end
                                                    end
                                                catch err2
                                                    #verbose && println(sprint(showerror, err2))
                                                end
                                            end
                                        end
                                    end
                                catch err1
                                    # verbose && println(sprint(showerror, err1))
                                    # return
                                end
                            end
                        end
                    end
                    verbose && println()
                end
            elseif en.judgement && !istop(α)
                # T⪯
                verbose && println("T⪯")
                for l ∈ findleaves(en)
                    verbose && println(l)
                    ti = l
                    for γ in minimalmembers(a, α)
                        ti = MVHSTableau(
                            false,
                            (γ, φ),
                            en.interval,
                            l.constraintsystem,
                            ti
                        )
                        push!(metricheaps, ti)
                        verbose && println(ti)
                    end
                    verbose && println()
                end
            elseif !en.judgement && !istop(α)
                # F⪯
                verbose && println("F⪯")
                for l ∈ findleaves(en)
                    verbose && println(l)
                    for βi in minimalmembers(a, α)
                        ti = MVHSTableau(
                            true,
                            (βi, φ),
                            en.interval,
                            l.constraintsystem,
                            l
                        )
                        push!(metricheaps, ti)
                        verbose && println(ti)
                    end
                    verbose && println()
                end
            else
                # No condition matched, pushing node back into metricheaps
                push!(metricheaps, node)
            end
        end
    end
end

function mvhsalphasat(
    α::T,
    φ::Formula,
    a::FiniteHeytingAlgebra,
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
                        MVHSTableau(
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
    mvhsalphasat(metricheaps, choosenode, a; verbose)
end

function mvhsalphasat(
    α::T,
    φ::Formula,
    a::FiniteHeytingAlgebra,
    metric::Function;
    verbose::Bool=false
) where {
    T<:Truth
}
    mvhsalphasat(α, φ, a, roundrobin, metric; verbose)
end

function mvhsalphasat(
    α::T,
    φ::Formula,
    a::FiniteHeytingAlgebra;
    rng = Random.GLOBAL_RNG,
    verbose::Bool=false
) where {
    T<:Truth
}
    randombranch(_::MVHSTableau) = rand(rng, Int)
    mvhsalphasat(α, φ, a, randombranch; verbose)
end
