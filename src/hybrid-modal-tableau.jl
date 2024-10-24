struct HAFSLOS{N,A<:FiniteIndexAlgebra{N}}
    domain::Vector{Point}
    algebra::A
    mvlt::Dict{Tuple{Point,Point},FiniteIndexTruth}
    mveq::Dict{Tuple{Point,Point},FiniteIndexTruth}

    function HAFSLOS(
        domain::Vector{Point},
        algebra::A,
        mvlt::Dict{Tuple{Point,Point},FiniteIndexTruth},
        mveq::Dict{Tuple{Point,Point},FiniteIndexTruth}
    ) where {
        N,
        A<:FiniteIndexAlgebra{N}
    }
        if !isa(mvlt, Dict{Tuple{Point,Point},FiniteIndexTruth})
            mvlt = convert(Dict{Tuple{Point,Point},FiniteIndexTruth}, mvlt)
        end
        if !isa(mveq, Dict{Tuple{Point,Point},FiniteIndexTruth})
            mveq = convert(Dict{Tuple{Point,Point},FiniteIndexTruth}, mveq)
        end
        new{N,A}(domain, algebra, mvlt, mveq)
    end
end

function equal(a1::HAFSLOS, a2::HAFSLOS)
     if a1.domain == a2.domain && a1.algebra == a2.algebra &&
        a1.mvlt == a2.mvlt && a1.mveq == a2.mveq 
        return true
     else
        return false
     end
end

"""
Check if a structure (D, <, =) is a adequate fuzzy strictly linearly ordered set.

1. =(x,y) = 1 iff x = y
2. =(x,y) = =(y,x)
3. <(x,x) = 0
4. <(x,z) ⪰ <(x,y) ⋅ <(y,z)
5. if <(x,y) ≻ 0 and <(y,z) ≻ 0 then <(x,z) ≻ 0
6. if <(x,y) = 0 and <(y,x) = 0 then =(x,y) = 1
7. if =(x,y) ≻ 0 then <(x,y) ≺ 1
"""
function checkhafslos(hafslos::HAFSLOS)
    # check axioms 1...7
    for x ∈ hafslos.domain
        !istop(hafslos.mveq[(x,x)]) && error("(D,<,=) is not a HAFSLOS (1)")
        !isbot(hafslos.mvlt[(x,x)]) && error("(D,<,=) is not a HAFSLOS (3)")
        for y ∈ hafslos.domain
            istop(hafslos.mveq[(x,y)]) && x != y && error("(D,<,=) is not a HAFSLOS (1)")
            hafslos.mveq[(x,y)] != hafslos.mveq[(y,x)] && error("(D,<,=) is not a HAFSLOS (2)")
            if isbot(hafslos.mvlt[(x,y)]) && isbot(hafslos.mvlt[(y,x)])
                !istop(hafslos.mveq[(x,y)]) && error("(D,<,=) is not a HAFSLOS (6)")
            end
            if !isbot(hafslos.mveq[(x,y)])
                istop(hafslos.mvlt[(x,y)]) && error("(D,<,=) is not a HAFSLOS (7)")
            end
            for z ∈ hafslos.domain
                !succeedeq(
                    hafslos.algebra,
                    hafslos.mvlt[(x,z)],
                    hafslos.algebra.meet(hafslos.mvlt[(x,y)], hafslos.mvlt[(y,z)])
                ) && error("(D,<,=) is not a HAFSLOS (4)")
                if !isbot(hafslos.mvlt[(x,y)]) && !isbot(hafslos.mvlt[(y,z)])
                    isbot(hafslos.mvlt[(x,z)]) && error("(D,<,=) is not a HAFSLOS (5)")
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
    c::HAFSLOS
) where {
    R<:AbstractRelation
}
    if r == SoleLogics.IA_A
        return c.mveq[(y,z)]
    elseif r == SoleLogics.IA_L
        return c.mvlt[(y,z)]
    elseif r == SoleLogics.IA_B
        return c.algebra.meet(c.mveq[(x,z)], c.mvlt[(t,y)])
    elseif r == SoleLogics.IA_E
        return c.algebra.meet(c.mvlt[(x,z)], c.mveq[(y,t)])
    elseif r == SoleLogics.IA_D
        return c.algebra.meet(c.mvlt[(x,z)], c.mvlt[(t,y)])
    elseif r == SoleLogics.IA_O
        return c.algebra.meet(c.algebra.meet(c.mvlt[(x,z)], c.mvlt[(z,y)]), c.mvlt[(y,t)])
    elseif r == SoleLogics.IA_Ai
        return c.mveq[(t,x)]
    elseif r == SoleLogics.IA_Li
        return c.mvlt[(t,x)]
    elseif r == SoleLogics.IA_Bi
        return c.algebra.meet(c.mveq[(z,x)], c.mvlt[(y,t)])
    elseif r == SoleLogics.IA_Ei
        return c.algebra.meet(c.mvlt[(z,x)], c.mveq[(t,y)])
    elseif r == SoleLogics.IA_Di
        return c.algebra.meet(c.mvlt[(z,x)], c.mvlt[(y,t)])
    elseif r == SoleLogics.IA_Oi
        return c.algebra.meet(c.algebra.meet(c.mvlt[(z,x)], c.mvlt[(x,t)]), c.mvlt[(t,y)])
    else
        error("Relation $r not in HS")
    end
end

mutable struct HybridMVHSTableau{T<:Truth} <: AbstractTableau
    const judgement::Bool
    const boundingimplication::Union{
        Tuple{T,Formula},
        Tuple{Formula,T},
        Tuple{T,T}
    }
    const interval::Interval
    constraintsystem::Union{HAFSLOS,Nothing}
    const father::Union{HybridMVHSTableau,Nothing}
    children::Vector{HybridMVHSTableau}
    expanded::Bool
    closed::Bool
    smtconstraints::Vector{String}

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
        # if isa(boundingimplication, Tuple{T1,Formula})
        #     if !isa(boundingimplication, Tuple{T,Formula})
        #         boundingimplication = (
        #             convert(T, boundingimplication[1]),
        #             boundingimplication[2]
        #         )
        #     end
        # elseif isa(boundingimplication, Tuple{Formula,T1})
        #     if !isa(boundingimplication, Tuple{Formula,T})
        #         boundingimplication = (
        #             boundingimplication[1],
        #             convert(T, boundingimplication[2]),
        #         )
        #     end
        # elseif isa(boundingimplication, Tuple{T1,T2})
        #     if !isa(boundingimplication, Tuple{T,T})
        #         boundingimplication = (
        #             convert(T, boundingimplication[1]),
        #             convert(T, boundingimplication[2]),
        #         )
        #     end
        # else
        #     error("Unexpected error")
        # end
        return new{T}(
            judgement,
            boundingimplication,
            interval,
            nothing,
            nothing,
            Vector{HybridMVHSTableau}(),
            false,
            false,
            Vector{String}()
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
        constraintsystem::HAFSLOS
    ) where{
        T<:Truth,
        T1<:Truth,
        T2<:Truth
    }
        # if isa(boundingimplication, Tuple{T1,Formula})
        #     if !isa(boundingimplication, Tuple{T,Formula})
        #         boundingimplication = (
        #             convert(T, boundingimplication[1]),
        #             boundingimplication[2]
        #         )
        #     end
        # elseif isa(boundingimplication, Tuple{Formula,T1})
        #     if !isa(boundingimplication, Tuple{Formula,T})
        #         boundingimplication = (
        #             boundingimplication[1],
        #             convert(T, boundingimplication[2]),
        #         )
        #     end
        # elseif isa(boundingimplication, Tuple{T1,T2})
        #     if !isa(boundingimplication, Tuple{T,T})
        #         boundingimplication = (
        #             convert(T, boundingimplication[1]),
        #             convert(T, boundingimplication[2]),
        #         )
        #     end
        # else
        #     error("Unexpected error")
        # end
        return new{T}(
            judgement,
            boundingimplication,
            interval,
            constraintsystem,
            nothing,
            Vector{HybridMVHSTableau}(),
            false,
            false,
            Vector{String}()
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
        constraintsystem::HAFSLOS,
        father::HybridMVHSTableau
    ) where{
        T<:Truth,
        T1<:Truth,
        T2<:Truth
    }
        # if isa(boundingimplication, Tuple{T1,Formula})
        #     if !isa(boundingimplication, Tuple{T,Formula})
        #         boundingimplication = (
        #             convert(T, boundingimplication[1]),
        #             boundingimplication[2]
        #         )
        #     end
        # elseif isa(boundingimplication, Tuple{Formula,T1})
        #     if !isa(boundingimplication, Tuple{Formula,T})
        #         boundingimplication = (
        #             boundingimplication[1],
        #             convert(T, boundingimplication[2]),
        #         )
        #     end
        # elseif isa(boundingimplication, Tuple{T1,T2})
        #     if !isa(boundingimplication, Tuple{T,T})
        #         boundingimplication = (
        #             convert(T, boundingimplication[1]),
        #             convert(T, boundingimplication[2]),
        #         )
        #     end
        # else
        #     error("Unexpected error")
        # end
        t = new{T}(
            judgement,
            boundingimplication,
            interval,
            constraintsystem,
            father,
            Vector{HybridMVHSTableau}(),
            false,
            false,
            father.smtconstraints
        )
        pushchildren!(father, t)
        return t
    end

    function HybridMVHSTableau{T}(
        judgement::Bool,
        boundingimplication::Union{
            Tuple{T1,Formula},
            Tuple{Formula,T1},
            Tuple{T1,T2}
        },
        interval::Interval,
        constraintsystem::HAFSLOS,
        father::HybridMVHSTableau,
        newsmtconstraints::Vector{String}
    ) where{
        T<:Truth,
        T1<:Truth,
        T2<:Truth
    }
        # if isa(boundingimplication, Tuple{T1,Formula})
        #     if !isa(boundingimplication, Tuple{T,Formula})
        #         boundingimplication = (
        #             convert(T, boundingimplication[1]),
        #             boundingimplication[2]
        #         )
        #     end
        # elseif isa(boundingimplication, Tuple{Formula,T1})
        #     if !isa(boundingimplication, Tuple{Formula,T})
        #         boundingimplication = (
        #             boundingimplication[1],
        #             convert(T, boundingimplication[2]),
        #         )
        #     end
        # elseif isa(boundingimplication, Tuple{T1,T2})
        #     if !isa(boundingimplication, Tuple{T,T})
        #         boundingimplication = (
        #             convert(T, boundingimplication[1]),
        #             convert(T, boundingimplication[2]),
        #         )
        #     end
        # else
        #     error("Unexpected error")
        # end
        t = new{T}(
            judgement,
            boundingimplication,
            interval,
            constraintsystem,
            father,
            Vector{HybridMVHSTableau}(),
            false,
            false,
            [father.smtconstraints; newsmtconstraints]
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
    ft::HybridMVHSTableau,
    a::A
) where {
    N,
    A<:FiniteIndexAlgebra{N}
}
    en = ft
    s = en.judgement
    z = en.boundingimplication
    if z[1] isa Truth
        if s            
            while !isroot(ft)
                ft = ft.father
                y = ft.boundingimplication
                if y[1] isa Truth && !ft.judgement && z[2] == y[2]
                    # X5
                    if z[1] ∉ getdomain(a)
                        if y[1] ∉ getdomain(a)
                            for l ∈ leaves(en)
                                addconstraint!(l, "(assert (not (precedeq $(y[1].label) $(z[1].label))))\n")
                            end
                        else
                            for l ∈ leaves(en)
                                addconstraint!(l, "(assert (not (precedeq a$(y[1].index) $(z[1].label))))\n")
                            end
                        end
                    else 
                        if y[1] ∉ getdomain(a)
                            for l ∈ leaves(en)
                                addconstraint!(l, "(assert (not (precedeq $(y[1].label) a$(z[1].index))))\n")
                            end
                        elseif precedeq(a, y[1], z[1])
                            return true
                        end
                    end
                elseif y[2] isa Truth && ft.judgement && z[2] == y[1]
                    # X6
                    if z[1] ∉ getdomain(a)
                        if y[2] ∉ getdomain(a)
                            for l ∈ leaves(en)
                                addconstraint!(l, "(assert (precedeq $(z[1].label) $(y[2].label)))\n")
                            end
                        else
                            for l ∈ leaves(en)
                                addconstraint!(l, "(assert (precedeq $(z[1].label) a$(y[2].index)))\n")
                            end
                        end
                    else
                        if y[2] ∉ getdomain(a)
                            for l ∈ leaves(en)
                                addconstraint!(l, "(assert (precedeq a$(z[1].index) $(y[2].label)))\n")
                            end
                        elseif !precedeq(a, z[1], y[2])
                            return true
                        end
                    end
                end
            end            
        else
            while !isroot(ft)
                ft = ft.father
                y = ft.boundingimplication
                if y[1] isa Truth && ft.judgement && z[2] == y[2]
                    # X5
                    if z[1] ∉ getdomain(a)
                        if y[1] ∉ getdomain(a)
                            for l ∈ leaves(en)
                                addconstraint!(l, "(assert (not (precedeq $(z[1].label) $(y[1].label))))\n")
                            end
                        else
                            for l ∈ leaves(en)
                                addconstraint!(l, "(assert (not (precedeq $(z[1].label) a$(y[1].index))))\n")
                            end
                        end
                    else
                        if y[1] ∉ getdomain(a)
                            for l ∈ leaves(en)
                                addconstraint!(l, "(assert (not (precedeq a$(z[1].index) $(y[1].label))))\n")
                            end
                        elseif precedeq(a, z[1], y[1])
                            return true
                        end
                    end
                elseif y[2] isa Truth && !ft.judgement && z[2] == y[1]
                    # X8
                    if z[1] ∉ getdomain(a)
                        if y[2] ∉ getdomain(a)
                            for l ∈ leaves(en)
                                addconstraint!(l, "(assert (not (precedeq $(z[1].label) $(y[2].label))))\n")
                            end
                        else
                            for l ∈ leaves(en)
                                addconstraint!(l, "(assert (not (precedeq $(z[1].label) a$(y[2].index))))\n")
                            end
                        end
                    else
                        if y[2] ∉ getdomain(a)
                            for l ∈ leaves(en)
                                addconstraint!(l, "(assert (not (precedeq a$(z[1].index) $(y[2].label))))\n")
                            end
                        elseif precedeq(a, z[1], y[2])
                            return true
                        end
                    end
                end
            end
        end
    elseif z[2] isa Truth
        if s
            while !isroot(ft)
                ft = ft.father
                y = ft.boundingimplication
                if y[1] isa Truth && ft.sign && z[1] == y[2]
                    # X6
                    if z[2] ∉ getdomain(a)
                        if y[1] ∉ getdomain(a)
                            for l ∈ leaves(en)
                                addconstraint!(l, "(assert (precedeq $(y[1].label) $(z[2].label)))\n")
                            end
                        else
                            for l ∈ leaves(en)
                                addconstraint!(l, "(assert (precedeq a$(y[1].index) $(z[2].label)))\n")
                            end
                        end
                    else
                        if y[1] ∉ getdomain(a)
                            for l ∈ leaves(en)
                                addconstraint!(l, "(assert (precedeq $(y[1].label) a$(z[2].index)))\n")
                            end
                        elseif !precedeq(a, y[1], z[2])
                            return true
                        end
                    end
                elseif y[2] isa Truth && !ft.sign && z[1] == y[1]
                    # X7
                    if z[2] ∉ getdomain(a)
                        if y[2] ∉ getdomain(a)
                            for l ∈ leaves(en)
                                addconstraint!(l, "(assert (precedeq $(y[2].label) $(z[2].label)))\n")
                            end
                        else
                            for l ∈ leaves(en)
                                addconstraint!(l, "(assert (precedeq a$(y[2].index) $(z[2].label)))\n")
                            end
                        end
                    else
                        if y[2] ∉ getdomain(a)
                            for l ∈ leaves(en)
                                addconstraint!(l, "(assert (precedeq $(y[2].label) a$(z[2].index)))\n")
                            end
                        elseif !precedeq(a, y[2], z[2])
                            return true
                        end
                    end
                end
            end
        else
            while !isroot(ft)
                ft = ft.father
                y = ft.boundingimplication
                if y[2] isa Truth && ft.sign && z[1] == y[1]
                    # X7
                    if z[2] ∉ getdomain(a)
                        if y[2] ∉ getdomain(a)
                            for l ∈ leaves(en)
                                addconstraint!(l, "(assert (precedeq $(z[2].label) $(y[2].label)))\n")
                            end
                        else
                            for l ∈ leaves(en)
                                addconstraint!(l, "(assert (precedeq $(z[2].label) a$(y[2].index)))\n")
                            end
                        end
                    else
                        if y[2] ∉ getdomain(a)
                            for l ∈ leaves(en)
                                addconstraint!(l, "(assert (precedeq a$(z[2].index) $(y[2].label)))\n")
                            end
                        elseif !precedeq(a, z[2], y[2])
                            return true
                        end
                    end
                elseif y[1] isa Truth && !ft.sign && z[1] == y[2]
                    # X8
                    if z[2] ∉ getdomain(a)
                        if y[1] ∉ getdomain(a)
                            for l ∈ leaves(en)
                                addconstraint!(l, "(assert (not (precedeq $(y[1].label) $(z[2].label))))\n")
                            end
                        else
                            for l ∈ leaves(en)
                                addconstraint!(l, "(assert (not (precedeq a$(y[1].index) $(z[2].label))))\n")
                            end
                        end
                    else
                        if y[1] ∉ getdomain(a)
                            for l ∈ leaves(en)
                                addconstraint!(l, "(assert (not (precedeq $(y[1].label) a$(z[2].index))))\n")
                            end
                        elseif precedeq(a, y[1], z[2])
                            return true
                        end
                    end
                end
            end
        end
    end
    return false
end

using UUIDs

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
    # c::HAFSLOS
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
    a::A,
    roots::Vector{HybridMVHSTableau};
    verbose::Bool=false,
    timeout::Union{Nothing,Int}=nothing,
    diamondexpansion::Float64=1.0
) where {
    N,
    A<:FiniteIndexFLewAlgebra{N}
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
        if isexpanded(node) # found a (possibly) satisfiable branch
            if isempty(node.smtconstraints)
                verbose && println(node) # print satisfiable branch
                return true
            else
                # algebra
                smtfile = "(declare-sort A1)\n"
                for i ∈ 1:N
                    smtfile *= "(declare-const a$i A1)\n"
                end
                smtfile *= "(assert (distinct"
                for i ∈ 1:N
                    smtfile *= " a$i"
                end
                smtfile *= "))\n(declare-fun join (A1 A1) A1)\n(declare-fun meet (A1 A1) A1)\n(declare-fun monoid (A1 A1) A1)\n(declare-fun implication (A1 A1) A1)\n"
                for i ∈ 1:N
                    for j ∈ 1:N
                        smtfile *= "(assert (= (join a$i a$j) a$(a.join(UInt8(i), UInt8(j)).index)))\n"
                        smtfile *= "(assert (= (meet a$i a$j) a$(a.meet(UInt8(i), UInt8(j)).index)))\n"
                        smtfile *= "(assert (= (monoid a$i a$j) a$(a.monoid(UInt8(i), UInt8(j)).index)))\n"
                        smtfile *= "(assert (= (implication a$i a$j) a$(a.implication(UInt8(i), UInt8(j)).index)))\n"
                    end
                end
                smtfile *= "(define-fun precedeq ((x A1) (y A1)) Bool (= (meet x y) x))\n"
                # order
                smtfile *= "(declare-sort A2)\n"
                smtfile *= "(declare-fun mveq (A2 A2) A1)\n"
                smtfile *= "(declare-fun mvlt (A2 A2) A1)\n"
                smtfile *= "(declare-const x A2)\n(declare-const y A2)\n(declare-const z A2)\n"
                smtfile *= "(assert (= (= (mveq x y) a1) (= x y)))\n"                                                           # =(x,y) = 1 iff x = y
                smtfile *= "(assert (= (mveq x y) (mveq y x)))\n"                                                               # =(x,y) = =(y,x)
                smtfile *= "(assert (= (mvlt x x) a2))\n"                                                                       # <(x,x) = 0
                smtfile *= "(assert (precedeq (meet (mvlt x y) (mvlt y z)) (mvlt x z)))\n"                                      # <(x,z) ⪰ <(x,y) ⋅ <(y,z)
                smtfile *= "(assert (=> (and (distinct (mvlt x y) a2) (distinct (mvlt y z) a2)) (distinct (mvlt x z) a2)))\n"   # if <(x,y) ≻ 0 and <(y,z) ≻ 0 then <(x,z) ≻ 0
                smtfile *= "(assert (=> (and (= (mvlt x y) a2) (= (mvlt y x) a2)) (= (mveq x y) a1)))\n"                        # if <(x,y) = 0 and <(y,x) = 0 then =(x,y) = 1
                smtfile *= "(assert (=> (distinct (mveq x y) a2) (distinct (mvlt x y) a1)))"                                    # if =(x,y) ≻ 0 then <(x,y) ≺ 1
                # check smtconstraints
                for str ∈ node.smtconstraints
                    smtfile *= str * "\n"
                end
                smtfile *= "(check-sat)"
                b = IOBuffer()
                uuid = UUIDs.uuid4()
                touch("temp$uuid.smt2")
                open("temp$uuid.smt2", "w") do file
                    write(file, smtfile)
                end
                run(pipeline(`z3 temp$uuid.smt2`, stdout = b))
                rm("temp$uuid.smt2")
                if take!(b) == UInt8[0x73, 0x61, 0x74, 0x0a]
                    verbose && println(node) # print satisfiable branch
                    return true
                else
                    close!(node)
                end
            end
        else
            en = findexpansionnode(node)
            expand!(en)
            verbose && println("expansion node:")
            verbose && println(en)
            if en.boundingimplication isa Tuple{Truth, Truth}
                β = en.boundingimplication[1]
                γ = en.boundingimplication[2]
                # Branch Closure Conditions
                if en.judgement 
                    if β ∉ getdomain(a)
                        if γ ∉ getdomain(a)
                            for l ∈ leaves(en)
                                addconstraint!(l, "(assert (precedeq $(β.label) $(γ.label)))\n")
                            end
                        else
                            for l ∈ leaves(en)
                                addconstraint!(l, "(assert (precedeq $(β.label) a$(γ.index)))\n")
                            end
                        end
                    elseif γ ∉ getdomain(a)
                        for l ∈ leaves(en)
                            addconstraint!(l, "(assert (precedeq a$(β.index) $(γ.label)))\n")
                        end
                    elseif !precedeq(a, β, γ)
                        # T(a→b) where a≰b case
                        close!(en)
                    end
                else
                    if β ∉ getdomain(a)
                        if γ ∉ getdomain(a)
                            for l ∈ leaves(en)
                                addconstraint!(l, "(assert (not (precedeq $(β.label) $(γ.label))))\n")
                            end
                        elseif !istop(γ)
                            for l ∈ leaves(en)
                                addconstraint!(l, "(assert (not (precedeq $(β.label) a$(γ.index))))\n")
                            end
                        else
                            # F(X→⊤) case
                            close!(en)
                        end
                    elseif γ ∉ getdomain(a)
                        if !isbot(β)
                            for l ∈ leaves(en)
                                addconstraint!(l, "(assert (not (precedeq a$(β.index) $(γ.label))))\n")
                            end
                        else
                            # F(⊥→X) case
                            close!(en)
                        end
                    elseif precedeq(a, β, γ) && !isbot(β) && !istop(γ)
                        # F(a→b) where a≤b and a≠⊥ and b≠⊤ case
                        close!(en)
                    elseif !s && isbot(β)
                        # F(⊥→X) case
                        close!(en)
                    elseif !s && istop(γ)
                        # F(X→⊤) case
                        close!(en)
                    end
                end
                if findsimilar(en, a)
                    # T(b→X) and F(a→X) where a ≤ b case
                    close!(en)
                # Base case
                else
                    # let err
                    #     try
                    #         checkhafslos(en.constraintsystem)
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
                    pairs = Set{NTuple{2,FiniteIndexTruth}}()
                    for βi ∈ 1:N
                        for γi ∈ 1:N
                            if precedeq(a, β, a.monoid(FiniteIndexTruth(βi), FiniteIndexTruth(γi)))
                                push!(pairs, (FiniteIndexTruth(βi), FiniteIndexTruth(γi)))
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
                                t1 = HybridMVHSTableau{FiniteIndexTruth}(
                                true,
                                (pair[1], ψ),
                                en.interval,
                                l.constraintsystem,
                                l
                            )
                                push!(metricheaps, t1)
                                if !findtableau(t1, true, (pair[2], ε), en.interval)
                                        t2 = HybridMVHSTableau{FiniteIndexTruth}(
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
                                    t2 = HybridMVHSTableau{FiniteIndexTruth}(
                                        true,
                                        (pair[2], ε),
                                        en.interval,
                                        l.constraintsystem,
                                        l
                                    )
                                    push!(metricheaps, t2)
                                else  # Here there should be a branch and I need to keep track of it
                                    ti = HybridMVHSTableau{FiniteIndexTruth}(   # Fake node (always true)
                                        true,
                                        (FiniteIndexTruth(1), FiniteIndexTruth(1)),
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
                    pairs = Set{NTuple{2,FiniteIndexTruth}}()
                    for βi ∈ 1:N
                        for γi ∈ 1:N
                            if !precedeq(a, β, a.monoid(FiniteIndexTruth(βi), FiniteIndexTruth(γi)))
                                push!(pairs, (FiniteIndexTruth(βi), FiniteIndexTruth(γi)))
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
                                t1 = HybridMVHSTableau{FiniteIndexTruth}(
                                    true,
                                    (ψ, pair[1]),
                                    en.interval,
                                    l.constraintsystem,
                                    l
                                )
                                push!(metricheaps, t1)
                                if !findtableau(t1, true, (ε, pair[2]), en.interval)
                                    t2 = HybridMVHSTableau{FiniteIndexTruth}(
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
                                    t2 = HybridMVHSTableau{FiniteIndexTruth}(
                                        true,
                                        (ε, pair[2]),
                                        en.interval,
                                        l.constraintsystem,
                                        l
                                    )
                                    push!(metricheaps, t2)
                                else  # Here there should be a branch and I need to keep track of it
                                    ti = HybridMVHSTableau{FiniteIndexTruth}(   # Fake node (always true)
                                        true,
                                        (FiniteIndexTruth(1), FiniteIndexTruth(1)),
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
                    pairs = Set{NTuple{2,FiniteIndexTruth}}()
                    for βi ∈ 1:N
                        for γi ∈ 1:N
                            if precedeq(a, β, a.implication(FiniteIndexTruth(βi), FiniteIndexTruth(γi)))
                                push!(pairs, (FiniteIndexTruth(βi), FiniteIndexTruth(γi)))
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
                                t1 = HybridMVHSTableau{FiniteIndexTruth}(
                                    true,
                                    (ψ, pair[1]),
                                    en.interval,
                                    l.constraintsystem,
                                    l
                                )
                                push!(metricheaps, t1)
                                if !findtableau(t1, true, (pair[2], ε), en.interval)
                                        t2 = HybridMVHSTableau{FiniteIndexTruth}(
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
                                    t2 = HybridMVHSTableau{FiniteIndexTruth}(
                                        true,
                                        (pair[2], ε),
                                        en.interval,
                                        l.constraintsystem,
                                        l
                                    )
                                    push!(metricheaps, t2)
                                else  # Here there should be a branch and I need to keep track of it
                                    ti = HybridMVHSTableau{FiniteIndexTruth}(   # Fake node (always true)
                                        true,
                                        (FiniteIndexTruth(1), FiniteIndexTruth(1)),
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
                    pairs = Set{NTuple{2,FiniteIndexTruth}}()
                    for βi ∈ 1:N
                        for γi ∈ 1:N
                            if !precedeq(a, β, a.implication(FiniteIndexTruth(βi), FiniteIndexTruth(γi)))
                                push!(pairs, (FiniteIndexTruth(βi), FiniteIndexTruth(γi)))
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
                                t1 = HybridMVHSTableau{FiniteIndexTruth}(
                                    true,
                                    (pair[1], ψ),
                                    en.interval,
                                    l.constraintsystem,
                                    l
                                )
                                push!(metricheaps, t1)
                                if !findtableau(t1, true, (ε, pair[2]), en.interval)
                                    t2 = HybridMVHSTableau{FiniteIndexTruth}(
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
                                    t2 = HybridMVHSTableau{FiniteIndexTruth}(
                                        true,
                                        (ε, pair[2]),
                                        en.interval,
                                        l.constraintsystem,
                                        l
                                    )
                                    push!(metricheaps, t2)
                                else  # Here there should be a branch and I need to keep track of it
                                    ti = HybridMVHSTableau{FiniteIndexTruth}(   # Fake node (always true)
                                        true,
                                        (FiniteIndexTruth(1), FiniteIndexTruth(1)),
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
                elseif en.judgement && token(φ) isa BoxRelationalConnective && !isbot(β)
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
                                if !isbot(βi) && !isbot(a.meet(β, βi))
                                    # Optimization 1 (int. node)
                                    if !findtableau(tj,true,(a.meet(β, βi), φ.children[1]),Interval(zi,ti))
                                        tj = HybridMVHSTableau{FiniteIndexTruth}(
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
                            tj = HybridMVHSTableau{FiniteIndexTruth}(
                                true,
                                (β, φ),
                                en.interval,
                                cB,
                                tj
                            )
                            push!(metricheaps, tj)
                        end
                    end
                elseif !en.judgement && token(φ) isa BoxRelationalConnective && !isbot(β)
                    # F□"
                    verbose && println("F□")
                    for l ∈ findleaves(en)

                        newleaves = false

                        r = SoleLogics.relation(token(φ))
                        (x, y) = (en.interval.x, en.interval.y)
                        cB0 = l.constraintsystem

                        # cB0 = o(cB)
                        for zi ∈ cB0.domain
                            for ti ∈ cB0.domain
                                isbot(cB0.mvlt[(zi,ti)]) && continue # <(zi,ti) ≻ 0
                                βi = mveval(r, (x,y), (zi,ti), cB0)
                                if !isbot(βi) && !isbot(a.meet(β, βi))
                                    tj = HybridMVHSTableau{FiniteIndexTruth}(
                                        false,
                                        (a.meet(βi, β), φ.children[1]),
                                        Interval(zi,ti),
                                        cB0,
                                        l
                                    )
                                    push!(metricheaps, tj)
                                    newleaves = true
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
                        Threads.@threads for ltzcombs ∈ shuffle(combs)[1:ceil(Int, ncombs*diamondexpansion)]    # ceil and not floor!! (at least one)
                            for gtzcombs ∈ shuffle(combs)[1:ceil(Int, ncombs*diamondexpansion)]
                                for eqzcombs ∈ shuffle(combs)[1:ceil(Int, ncombs*diamondexpansion)]
                                    # Must initialize at every (parallel) cycle!
                                    # cB1 = o(cB) ∪ {z}
                                    z = Point(Char(Int(last(cB0.domain).label)+1))
                                    cB1 = HAFSLOS(
                                        vcat(cB0.domain, z),
                                        cB0.algebra,
                                        Dict(cB0.mvlt),
                                        Dict(cB0.mveq)
                                    )
                                    cB1.mvlt[(z,z)] = FiniteIndexTruth(2)
                                    cB1.mveq[(z,z)] = FiniteIndexTruth(1)
                
                                    # cB2 = cB1 ∪ {t} = o(cB) ∪ {z,t}
                                    t = Point(Char(Int(last(cB1.domain).label)+1))

                                    for i ∈ 1:length(cB0.domain)
                                        cB1.mvlt[(cB0.domain[i],z)] = ltzcombs[i]
                                        cB1.mvlt[(z,cB0.domain[i])] = gtzcombs[i]
                                        cB1.mveq[(cB0.domain[i],z)] = eqzcombs[i]
                                        cB1.mveq[(z,cB0.domain[i])] = eqzcombs[i]
                                    end
                                    try
                                        checkhafslos(cB1)
                                        # in general, < is not commutative!
                                        for zi ∈ cB0.domain
                                            isbot(cB1.mvlt[(zi,z)]) && continue # <(zi,z) ≻ 0
                                            βi = mveval(r, (x,y), (zi,z), cB1)
                                            if !isbot(βi) && !isbot(a.meet(β, βi))
                                                Threads.lock(u) do
                                                    tj = HybridMVHSTableau{FiniteIndexTruth}(
                                                        false,
                                                        (a.meet(βi, β), φ.children[1]),
                                                        Interval(zi,z),
                                                        cB1,
                                                        l
                                                    )
                                                    push!(metricheaps, tj)
                                                    newleaves = true
                                                end
                                            end
                                        end
                                        for ti ∈ cB0.domain
                                            isbot(cB1.mvlt[(z,ti)]) && continue # <(z,ti) ≻ 0
                                            βi = mveval(r, (x,y), (z,ti), cB1)
                                            if !isbot(βi) && !isbot(a.meet(β, βi))
                                                Threads.lock(u) do
                                                    tj = HybridMVHSTableau{FiniteIndexTruth}(
                                                        false,
                                                        (a.meet(βi, β), φ.children[1]),
                                                        Interval(z,ti),
                                                        cB1,
                                                        l
                                                    )
                                                    push!(metricheaps, tj)
                                                    newleaves = true
                                                end
                                            end
                                        end

                                        # cB2 = cB1 ∪ {t} = o(cB) ∪ {z,t}
                                        cB2 = HAFSLOS(
                                            vcat(cB1.domain, t),
                                            cB1.algebra,
                                            Dict(cB1.mvlt),
                                            Dict(cB1.mveq)
                                        )
                                        cB2.mvlt[(t,t)] = FiniteIndexTruth(2)
                                        cB2.mveq[(t,t)] = FiniteIndexTruth(1)

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
                                                        checkhafslos(cB2)
                                                        # in general, < is not commutative!
                                                        if !isbot(cB2.mvlt[(z,t)])  # <(z,t) ≻ 0
                                                            βi = mveval(r, (x,y), (z,t), cB2)
                                                            if !isbot(βi) && !isbot(a.meet(β, βi))
                                                                Threads.lock(u) do
                                                                    tj = HybridMVHSTableau{FiniteIndexTruth}(
                                                                        false,
                                                                        (a.meet(βi, β), φ.children[1]),
                                                                        Interval(z,t),
                                                                        cB2,
                                                                        l
                                                                    )
                                                                    push!(metricheaps, tj)
                                                                    newleaves = true
                                                                end
                                                            end
                                                        else    # <(t,z) ≻ 0
                                                            βi = mveval(r, (x,y), (t,z), cB2)
                                                            if !isbot(βi) && !isbot(a.meet(β, βi))
                                                                Threads.lock(u) do
                                                                    tj = HybridMVHSTableau{FiniteIndexTruth}(
                                                                        false,
                                                                        (a.meet(βi, β), φ.children[1]),
                                                                        Interval(t,z),
                                                                        cB2,
                                                                        l
                                                                    )
                                                                    push!(metricheaps, tj)
                                                                    newleaves = true
                                                                end
                                                            end
                                                        end
                                                    catch err2
                                                        # verbose && println(sprint(showerror, err2))
                                                    end
                                                end
                                            end
                                        end
                                    catch err1
                                        # verbose && println(sprint(showerror, err1))
                                    end
                                end
                            end
                        end
                        !newleaves && close!(l)
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
                                ti = HybridMVHSTableau{FiniteIndexTruth}(
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
                                ti = HybridMVHSTableau{FiniteIndexTruth}(
                                    true,
                                    (φ, βi),
                                    en.interval,
                                    l.constraintsystem,
                                    l
                                )
                                push!(metricheaps, ti)
                            else  # Here there should be a branch and I need to keep track of it
                                ti = HybridMVHSTableau{FiniteIndexTruth}(   # Fake node (always true)
                                    true,
                                    (FiniteIndexTruth(1), FiniteIndexTruth(1)),
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
                    pairs = Set{NTuple{2,FiniteIndexTruth}}()
                    for βi ∈ 1:N
                        for γi ∈ 1:N
                            if precedeq(a, a.join(FiniteIndexTruth(βi), FiniteIndexTruth(γi)), β)
                                push!(pairs, (FiniteIndexTruth(βi), FiniteIndexTruth(γi)))
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
                                t1 = HybridMVHSTableau{FiniteIndexTruth}(
                                    true,
                                    (ψ, pair[1]),
                                    en.interval,
                                    l.constraintsystem,
                                    l
                                )
                                push!(metricheaps, t1)
                                if !findtableau(t1, true, (ε, pair[2]), en.interval)
                                    t2 = HybridMVHSTableau{FiniteIndexTruth}(
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
                                    t2 = HybridMVHSTableau{FiniteIndexTruth}(
                                        true,
                                        (ε, pair[2]),
                                        en.interval,
                                        l.constraintsystem,
                                        l
                                    )
                                    push!(metricheaps, t2)
                                else  # Here there should be a branch and I need to keep track of it
                                    ti = HybridMVHSTableau{FiniteIndexTruth}(   # Fake node (always true)
                                        true,
                                        (FiniteIndexTruth(1), FiniteIndexTruth(1)),
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
                    pairs = Set{NTuple{2,FiniteIndexTruth}}()
                    for βi ∈ 1:N
                        for γi ∈ 1:N
                            if !precedeq(a, a.join(FiniteIndexTruth(βi), FiniteIndexTruth(γi)), β)
                                push!(pairs, (FiniteIndexTruth(βi), FiniteIndexTruth(γi)))
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
                                t1 = HybridMVHSTableau{FiniteIndexTruth}(
                                    true,
                                    (pair[1], ψ),
                                    en.interval,
                                    l.constraintsystem,
                                    l
                                )
                                push!(metricheaps, t1)
                                if !findtableau(l, true, (pair[2], ε), en.interval)
                                    t2 = HybridMVHSTableau{FiniteIndexTruth}(
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
                                    t2 = HybridMVHSTableau{FiniteIndexTruth}(
                                        true,
                                        (pair[2], ε),
                                        en.interval,
                                        l.constraintsystem,
                                        l
                                    )
                                    push!(metricheaps, t2)
                                else  # Here there should be a branch and I need to keep track of it
                                    ti = HybridMVHSTableau{FiniteIndexTruth}(   # Fake node (always true)
                                        true,
                                        (FiniteIndexTruth(1), FiniteIndexTruth(1)),
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
                elseif en.judgement && token(φ) isa DiamondRelationalConnective && !istop(β)
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
                                if !istop(βi) && !istop(a.implication(βi, β))
                                    # Optimization 1 (int. node)
                                    if !findtableau(tj,true,(φ.children[1], a.implication(βi, β)),Interval(zi,ti))
                                        tj = HybridMVHSTableau{FiniteIndexTruth}(
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
                            tj = HybridMVHSTableau{FiniteIndexTruth}(
                                true,
                                (φ, β),
                                en.interval,
                                cB,
                                tj
                            )
                            push!(metricheaps, tj)
                        end
                    end
                elseif !en.judgement && token(φ) isa DiamondRelationalConnective && !istop(β)
                    # F◊
                    verbose && println("F◊")
                    for l ∈ findleaves(en)

                        newleaves = false

                        r = SoleLogics.relation(token(φ))
                        (x, y) = (en.interval.x, en.interval.y)
                        cB0 = l.constraintsystem

                        # cB0 = o(cB)
                        for zi ∈ cB0.domain
                            for ti ∈ cB0.domain
                                isbot(cB0.mvlt[(zi,ti)]) && continue # <(zi,ti) ≻ 0
                                βi = mveval(r, (x,y), (zi,ti), cB0)
                                if !istop(βi) && !istop(a.implication(βi, β))
                                    tj = HybridMVHSTableau{FiniteIndexTruth}(
                                        false,
                                        (φ.children[1], a.implication(βi, β)),
                                        Interval(zi,ti),
                                        cB0,
                                        l
                                    )
                                    push!(metricheaps, tj)
                                    newleaves = true
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
                        Threads.@threads for ltzcombs ∈ shuffle(combs)[1:ceil(Int, ncombs*diamondexpansion)]    # ceil and not floor!! (at least one)
                            for gtzcombs ∈ shuffle(combs)[1:ceil(Int, ncombs*diamondexpansion)]
                                for eqzcombs ∈ shuffle(combs)[1:ceil(Int, ncombs*diamondexpansion)]
                                    # Must initialize at every (parallel) cycle!
                                    # cB1 = o(cB) ∪ {z}
                                    z = Point(Char(Int(last(cB0.domain).label)+1))
                                    cB1 = HAFSLOS(
                                        vcat(cB0.domain, z),
                                        cB0.algebra,
                                        Dict(cB0.mvlt),
                                        Dict(cB0.mveq)
                                    )
                                    cB1.mvlt[(z,z)] = FiniteIndexTruth(2)
                                    cB1.mveq[(z,z)] = FiniteIndexTruth(1)

                                    # cB2 = cB1 ∪ {t} = o(cB) ∪ {z,t}
                                    t = Point(Char(Int(last(cB1.domain).label)+1))

                                    for i ∈ 1:length(cB0.domain)
                                        cB1.mvlt[(cB0.domain[i],z)] = ltzcombs[i]
                                        cB1.mvlt[(z,cB0.domain[i])] = gtzcombs[i]
                                        cB1.mveq[(cB0.domain[i],z)] = eqzcombs[i]
                                        cB1.mveq[(z,cB0.domain[i])] = eqzcombs[i]
                                    end
                                    try
                                        checkhafslos(cB1)
                                        # in general, < is not commutative!
                                        for zi ∈ cB0.domain
                                            isbot(cB1.mvlt[(zi,z)]) && continue # <(zi,z) ≻ 0
                                            βi = mveval(r, (x,y), (zi,z), cB1)
                                            if !istop(βi) && !istop(a.implication(βi, β))
                                                Threads.lock(u) do
                                                    tj = HybridMVHSTableau{FiniteIndexTruth}(
                                                        false,
                                                        (φ.children[1], a.implication(βi, β)),
                                                        Interval(zi,z),
                                                        cB1,
                                                        l
                                                    )
                                                    push!(metricheaps, tj)
                                                    newleaves = true
                                                end
                                            end
                                        end
                                        for ti ∈ cB0.domain
                                            isbot(cB1.mvlt[(z,ti)]) && continue # <(z,ti) ≻ 0
                                            βi = mveval(r, (x,y), (z,ti), cB1)
                                            if !istop(βi) && !istop(a.implication(βi, β))
                                                Threads.lock(u) do
                                                    tj = HybridMVHSTableau{FiniteIndexTruth}(
                                                        false,
                                                        (φ.children[1], a.implication(βi, β)),
                                                        Interval(z,ti),
                                                        cB1,
                                                        l
                                                    )
                                                    push!(metricheaps, tj)
                                                    newleaves = true
                                                end
                                            end
                                        end

                                        # cB2 = cB1 ∪ {t} = o(cB) ∪ {z,t}
                                        cB2 = HAFSLOS(
                                            vcat(cB1.domain, t),
                                            cB1.algebra,
                                            Dict(cB1.mvlt),
                                            Dict(cB1.mveq)
                                        )
                                        cB2.mvlt[(t,t)] = FiniteIndexTruth(2)
                                        cB2.mveq[(t,t)] = FiniteIndexTruth(1)

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
                                                        checkhafslos(cB2)
                                                        # in general, < is not commutative!
                                                        if !isbot(cB2.mvlt[(z,t)])  # <(z,t) ≻ 0
                                                            βi = mveval(r, (x,y), (z,t), cB2)
                                                            if !istop(βi) && !istop(a.implication(βi, β))
                                                                Threads.lock(u) do
                                                                    tj = HybridMVHSTableau{FiniteIndexTruth}(
                                                                        false,
                                                                        (φ.children[1], a.implication(βi, β)),
                                                                        Interval(z,t),
                                                                        cB2,
                                                                        l
                                                                    )
                                                                    push!(metricheaps, tj)
                                                                    newleaves = true
                                                                end
                                                            end
                                                        else    # <(t,z) ≻ 0
                                                            βi = mveval(r, (x,y), (t,z), cB2)
                                                            if !istop(βi) && !istop(a.implication(βi, β))
                                                                Threads.lock(u) do
                                                                    tj = HybridMVHSTableau{FiniteIndexTruth}(
                                                                        false,
                                                                        (φ.children[1], a.implication(βi, β)),
                                                                        Interval(t,z),
                                                                        cB2,
                                                                        l
                                                                    )
                                                                    push!(metricheaps, tj)
                                                                    newleaves = true
                                                                end
                                                            end
                                                        end
                                                    catch err2
                                                        # verbose && println(sprint(showerror, err2))
                                                    end
                                                end
                                            end
                                        end
                                    catch err1
                                        # verbose && println(sprint(showerror, err1))
                                    end
                                end
                            end
                        end
                        !newleaves && close!(l)
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
                                ti = HybridMVHSTableau{FiniteIndexTruth}(
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
                                ti = HybridMVHSTableau{FiniteIndexTruth}(
                                    true,
                                    (βi, φ),
                                    en.interval,
                                    l.constraintsystem,
                                    l
                                )
                                push!(metricheaps, ti)
                            else  # Here there should be a branch and I need to keep track of it
                                ti = HybridMVHSTableau{FiniteIndexTruth}(   # Fake node (always true)
                                    true,
                                    (FiniteIndexTruth(1), FiniteIndexTruth(1)),
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
    N,
    A<:FiniteIndexAlgebra{N},
    T1<:Truth
}
    if diamondexpansion < 0.0 || diamondexpansion > 1.0
        error("% diamond expansion must be between 0.0 and 1.0")
    end
    # if !isa(α, T) α = convert(T, α) end
    tableaux = Vector{HybridMVHSTableau}()
    x, y = Point.(['A', 'B'])
    for δ ∈ 1:N
        δ == 1 && continue    # (1), δ == 1 act as istop(δ)
        for β ∈ 1:N
            β == 2 && continue    # <(x,y) ≻ 0, β == 2 act as isbot(β)
            for γ ∈ 1:N
                hafslos = HAFSLOS(
                    [x, y],
                    a,
                    Dict(
                        (x,x) => FiniteIndexTruth(2), (x,y) => FiniteIndexTruth(β),
                        (y,x) => FiniteIndexTruth(γ), (y,y) => FiniteIndexTruth(2)
                    ),
                    Dict(
                        (x,x) => FiniteIndexTruth(1), (x,y) => FiniteIndexTruth(δ),
                        (y,x) => FiniteIndexTruth(δ), (y,y) => FiniteIndexTruth(1)
                    )
                )
                try
                    checkhafslos(hafslos)
                    push!(
                        tableaux,
                        HybridMVHSTableau{FiniteIndexTruth}(
                            true,
                            (α, φ),
                            Interval(x, y),
                            hafslos
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
    
    !isnothing(r) && !r && diamondexpansion < 1.0 && @warn "WARNING: α-sat returned $r with % diamond expansion set to $diamondexpansion"
    return r
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
    N,
    A<:FiniteIndexAlgebra{N},
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
    N,
    A<:FiniteIndexAlgebra{N},
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
    N,
    A<:FiniteIndexAlgebra{N},
    T1<:Truth
}
    if diamondexpansion < 0.0 || diamondexpansion > 1.0
        error("% diamond expansion must be between 0.0 and 1.0")
    end
    # if !isa(α, T) α = convert(T, α) end
    tableaux = Vector{HybridMVHSTableau}()
    x, y = Point.(['A', 'B'])
    for δ ∈ 1:N
        δ == 1 && continue    # (1), δ == 1 act as istop(δ)
        for β ∈ 1:N
            β == 2 && continue    # <(x,y) ≻ 0, β == 2 act as isbot(β)
            for γ ∈ 1:N
                hafslos = HAFSLOS(
                    [x, y],
                    a,
                    Dict(
                        (x,x) => FiniteIndexTruth(2), (x,y) => FiniteIndexTruth(β),
                        (y,x) => FiniteIndexTruth(γ), (y,y) => FiniteIndexTruth(2)
                    ),
                    Dict(
                        (x,x) => FiniteIndexTruth(1), (x,y) => FiniteIndexTruth(δ),
                        (y,x) => FiniteIndexTruth(δ), (y,y) => FiniteIndexTruth(1)
                    )
                )
                try
                    checkhafslos(hafslos)
                    push!(
                        tableaux,
                        HybridMVHSTableau{FiniteIndexTruth}(
                            false,
                            (α, φ),
                            Interval(x, y),
                            hafslos
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
    else
        r && diamondexpansion < 1.0 && @warn "WARNING: α-val returned $(!r) with % diamond expansion set to $diamondexpansion"
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
    N,
    A<:FiniteIndexAlgebra{N},
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
    N,
    A<:FiniteIndexAlgebra{N},
    T1<:Truth
}
    randombranch(_::HybridMVHSTableau) = rand(rng, Int)
    hybridmvhsalphaprove(α, φ, a, randombranch; verbose, timeout, diamondexpansion)
end
