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
    (z,t)::Tuple{Point,Point}
) where {
    R<:AbstractRelation
}
    if r == SoleLogics.IA_A
        "(mveq $(y.label) $(z.label))"
    elseif r == SoleLogics.IA_L
        "(mvlt $(y.label) $(z.label))"
    elseif r == SoleLogics.IA_B
        "(meet (mveq $(x.label) $(z.label)) (mvlt $(t.label) $(y.label)))"
    elseif r == SoleLogics.IA_E
        "(meet (mvlt $(x.label) $(z.label)) (mveq $(y.label) $(t.label)))"
    elseif r == SoleLogics.IA_D
        "(meet (mvlt $(x.label) $(z.label)) (mvlt $(t.label) $(y.label)))"
    elseif r == SoleLogics.IA_O
        "(meet (meet (mvlt $(x.label) $(z.label)) (mvlt $(z.label) $(y.label))) (mvlt $(y.label) $(t.label))"
    elseif r == SoleLogics.IA_Ai
        "(mveq $(t.label) $(x.label))"
    elseif r == SoleLogics.IA_Li
        "(mvlt $(t.label) $(x.label))"
    elseif r == SoleLogics.IA_Bi
        "(meet (mveq $(z.label) $(x.label)) (mvlt $(y.label) $(t.label)))"
    elseif r == SoleLogics.IA_Ei
        "(meet (mvlt $(z.label) $(x.label)) (mveq $(t.label) $(y.label)))"
    elseif r == SoleLogics.IA_Di
        "(meet (mvlt $(z.label) $(x.label)) (mvlt $(y.label) $(t.label)))"
    elseif r == SoleLogics.IA_Oi
        "(meet (meet (mvlt $(z.label) $(x.label)) (mvlt $(x.label) $(t.label))) (mvlt $(t.label) $(y.label))"
    else
        error("Relation $r not in HS")
    end
end

mutable struct HybridMVHSTableau{T<:Truth} <: AbstractTableau
    const judgement::Bool
    const boundingimplication::Union{
        Tuple{Truth,Formula},
        Tuple{Formula,Truth},
        Tuple{Truth,Truth}
    }
    const interval::Tuple{Point,Point}
    const constraintsystem::Vector{Point}
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
        interval::Tuple{Point,Point},
        newsmtconstraints::Vector{String}
    ) where {
        T<:Truth,
        T1<:Truth,
        T2<:Truth
    }
        return new{T}(
            judgement,
            boundingimplication,
            interval,
            nothing,
            nothing,
            Vector{HybridMVHSTableau}(),
            false,
            false,
            newsmtconstraints
        )
    end

    function HybridMVHSTableau{T}(
        judgement::Bool,
        boundingimplication::Union{
            Tuple{T1,Formula},
            Tuple{Formula,T1},
            Tuple{T1,T2}
        },
        interval::Tuple{Point,Point},
        constraintsystem::Vector{Point},
        newsmtconstraints::Vector{String}
    ) where{
        T<:Truth,
        T1<:Truth,
        T2<:Truth
    }
        return new{T}(
            judgement,
            boundingimplication,
            interval,
            constraintsystem,
            nothing,
            Vector{HybridMVHSTableau}(),
            false,
            false,
            newsmtconstraints
        )
    end

    function HybridMVHSTableau{T}(
        judgement::Bool,
        boundingimplication::Union{
            Tuple{T1,Formula},
            Tuple{Formula,T1},
            Tuple{T1,T2}
        },
        interval::Tuple{Point,Point},
        constraintsystem::Vector{Point},
        father::HybridMVHSTableau,
    ) where{
        T<:Truth,
        T1<:Truth,
        T2<:Truth
    }
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
        interval::Tuple{Point,Point},
        constraintsystem::Vector{Point},
        father::HybridMVHSTableau,
        newsmtconstraints::Vector{String}
    ) where{
        T<:Truth,
        T1<:Truth,
        T2<:Truth
    }
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
    if !isroot(t)
        filter!(e->e≠t,t.father.children)
        if isempty(t.father.children)
            close!(t.father)
        end
    end
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

addconstraint!(ft::HybridMVHSTableau, c::String) = push!(ft.smtconstraints, c)

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
                if y[1] isa Truth && ft.judgement && z[1] == y[2]
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
                elseif y[2] isa Truth && !ft.judgement && z[1] == y[1]
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
                if y[2] isa Truth && ft.judgement && z[1] == y[1]
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
                elseif y[1] isa Truth && !ft.judgement && z[1] == y[2]
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
    i::Tuple{Point,Point}
) where {
    T<:Truth
}
    t.judgement == j && t.boundingimplication == φ && t.interval == i && return true
    while !isroot(t)
        t = t.father
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
    algebra::A;
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
                        smtfile *= "(assert (= (join a$i a$j) a$(algebra.join(UInt8(i), UInt8(j)).index)))\n"
                        smtfile *= "(assert (= (meet a$i a$j) a$(algebra.meet(UInt8(i), UInt8(j)).index)))\n"
                        smtfile *= "(assert (= (monoid a$i a$j) a$(algebra.monoid(UInt8(i), UInt8(j)).index)))\n"
                        smtfile *= "(assert (= (implication a$i a$j) a$(algebra.implication(UInt8(i), UInt8(j)).index)))\n"
                    end
                end
                smtfile *= "(define-fun precedeq ((x A1) (y A1)) Bool (= (meet x y) x))\n"
                # order
                smtfile *= "(declare-sort A2)\n"
                smtfile *= "(declare-fun mveq (A2 A2) A1)\n"
                smtfile *= "(declare-fun mvlt (A2 A2) A1)\n"
                smtfile *= "(assert (forall ((x A2) (y A2)) (= (= (mveq x y) a1) (= x y))))\n"                                                                   # =(x,y) = 1 iff x = y
                smtfile *= "(assert (forall ((x A2) (y A2)) (= (mveq x y) (mveq y x))))\n"                                                                       # =(x,y) = =(y,x)
                smtfile *= "(assert (forall ((x A2)) (= (mvlt x x) a2)))\n"                                                                                      # <(x,x) = 0
                smtfile *= "(assert (forall ((x A2) (y A2) (z A2)) (precedeq (meet (mvlt x y) (mvlt y z)) (mvlt x z))))\n"                                       # <(x,z) ⪰ <(x,y) ⋅ <(y,z)
                smtfile *= "(assert (forall ((x A2) (y A2) (z A2)) (=> (and (distinct (mvlt x y) a2) (distinct (mvlt y z) a2)) (distinct (mvlt x z) a2))))\n"    # if <(x,y) ≻ 0 and <(y,z) ≻ 0 then <(x,z) ≻ 0
                smtfile *= "(assert (forall ((x A2) (y A2)) (=> (and (= (mvlt x y) a2) (= (mvlt y x) a2)) (= (mveq x y) a1))))\n"                                # if <(x,y) = 0 and <(y,x) = 0 then =(x,y) = 1
                smtfile *= "(assert (forall ((x A2) (y A2)) (=> (distinct (mveq x y) a2) (distinct (mvlt x y) a1))))\n"                                          # if =(x,y) ≻ 0 then <(x,y) ≺ 1
                # check smtconstraints
                for str ∈ node.smtconstraints
                    smtfile *= str * "\n"
                end
                smtfile *= "(check-sat)"
                b = IOBuffer()
                uuid = UUIDs.uuid4()
                touch("$(tempdir())/temp$uuid.smt2")
                open("$(tempdir())/temp$uuid.smt2", "w") do file
                    write(file, smtfile)
                end
                run(pipeline(`z3 $(tempdir())/temp$uuid.smt2`, stdout = b))
                # rm("$(tempdir())/temp$uuid.smt2")
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
                    if β ∉ getdomain(algebra)
                        if γ ∉ getdomain(algebra)
                            for l ∈ leaves(en)
                                addconstraint!(l, "(assert (precedeq $(β.label) $(γ.label)))\n")
                            end
                        else
                            for l ∈ leaves(en)
                                addconstraint!(l, "(assert (precedeq $(β.label) a$(γ.index)))\n")
                            end
                        end
                    elseif γ ∉ getdomain(algebra)
                        for l ∈ leaves(en)
                            addconstraint!(l, "(assert (precedeq a$(β.index) $(γ.label)))\n")
                        end
                    elseif !precedeq(algebra, β, γ)
                        # T(a→b) where a≰b case
                        close!(en)
                    end
                else
                    if β ∉ getdomain(algebra)
                        if γ ∉ getdomain(algebra)
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
                    elseif γ ∉ getdomain(algebra)
                        if !isbot(β)
                            for l ∈ leaves(en)
                                addconstraint!(l, "(assert (not (precedeq a$(β.index) $(γ.label))))\n")
                            end
                        else
                            # F(⊥→X) case
                            close!(en)
                        end
                    elseif precedeq(algebra, β, γ) && !isbot(β) && !istop(γ)
                        # F(a→b) where a≤b and a≠⊥ and b≠⊤ case
                        close!(en)
                    elseif !en.judgement && isbot(β)
                        # F(⊥→X) case
                        close!(en)
                    elseif !en.judgement && istop(γ)
                        # F(X→⊤) case
                        close!(en)
                    end
                end
                if findsimilar(en, algebra)
                    # T(b→X) and F(a→X) where a ≤ b case
                    close!(en)
                # Base case
                else
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
                elseif findsimilar(en, algebra)
                    # X5
                    verbose && println("X5")
                    close!(en)

                # Strong conjunction Rules 1
                elseif en.judgement && token(φ) isa NamedConnective{:∧} && !isbot(β)
                    # T(t→(A∧B)) case
                    (a, b) = children(φ)
                    x, y = FiniteTruth.(["x$(string(cycle))", "y$(string(cycle))"])
                    xsmtc = "(assert (or"
                    ysmtc = "(assert (or"
                    for value in 1:N
                        xsmtc *= " (= x$(string(cycle)) a$(string(value)))"
                        ysmtc *= " (= y$(string(cycle)) a$(string(value)))"
                    end
                    xsmtc *= "))\n"
                    ysmtc *= "))\n"
                    newsmtc = [
                        "(declare-const x$(string(cycle)) A1)",
                        "(declare-const y$(string(cycle)) A1)",
                        xsmtc,
                        ysmtc
                    ]
                    if isa(β, FiniteIndexTruth)
                        push!(newsmtc,"(assert (precedeq a$(β.index) (monoid x$(string(cycle)) y$(string(cycle)))))")
                    elseif isa(β, FiniteTruth)
                        push!(newsmtc,"(assert (precedeq $(β.label) (monoid x$(string(cycle)) y$(string(cycle)))))")
                    else
                        error("Wrong truth type")
                    end                
                    for l in leaves(en)                    
                        fta = HybridMVHSTableau{FiniteIndexTruth}(true, (x, a), en.interval, l.constraintsystem, l)
                        push!(metricheaps, fta)
                        ftb = HybridMVHSTableau{FiniteIndexTruth}(true, (y, b), en.interval, fta.constraintsystem, fta, newsmtc)
                        push!(metricheaps, ftb)
                    end                
                elseif !en.judgement && token(φ) isa NamedConnective{:∧} && !isbot(β)
                    # F(t→(A∧B)) case
                    (a, b) = children(φ)
                    x, y = FiniteTruth.(["x$(string(cycle))", "y$(string(cycle))"])
                    xsmtc = "(assert (or"
                    ysmtc = "(assert (or"
                    for value in 1:N
                        xsmtc *= " (= x$(string(cycle)) a$(string(value)))"
                        ysmtc *= " (= y$(string(cycle)) a$(string(value)))"
                    end
                    xsmtc *= "))\n"
                    ysmtc *= "))\n"
                    newsmtc = [
                        "(declare-const x$(string(cycle)) A1)",
                        "(declare-const y$(string(cycle)) A1)",
                        xsmtc,
                        ysmtc
                    ]
                    if isa(β, FiniteIndexTruth)
                        push!(newsmtc,"(assert (not (precedeq a$(β.index) (monoid x$(string(cycle)) y$(string(cycle))))))")
                    elseif isa(β, FiniteTruth)
                        push!(newsmtc,"(assert (not (precedeq $(β.label) (monoid x$(string(cycle)) y$(string(cycle))))))")
                    else
                        error("Wrong truth type")
                    end
                    for l in leaves(en)                    
                        fta = HybridMVHSTableau{FiniteIndexTruth}(true, (a, x), en.interval, l.constraintsystem, l)
                        push!(metricheaps, fta)
                        ftb = HybridMVHSTableau{FiniteIndexTruth}(true, (b, y), en.interval, fta.constraintsystem, fta, newsmtc)
                        push!(metricheaps, ftb)
                    end
                # Strong disjunction rules 2
                elseif en.judgement && token(φ) isa NamedConnective{:∨} && !isbot(β)
                    # T(t→(A∨B)) case
                    (a, b) = children(φ)
                    x, y = FiniteTruth.(["x$(string(cycle))", "y$(string(cycle))"])
                    xsmtc = "(assert (or"
                    ysmtc = "(assert (or"
                    for value in 1:N
                        xsmtc *= " (= x$(string(cycle)) a$(string(value)))"
                        ysmtc *= " (= y$(string(cycle)) a$(string(value)))"
                    end
                    xsmtc *= "))\n"
                    ysmtc *= "))\n"
                    newsmtc = [
                        "(declare-const x$(string(cycle)) A1)",
                        "(declare-const y$(string(cycle)) A1)",
                        xsmtc,
                        ysmtc                    
                    ]
                    if isa(β, FiniteIndexTruth)
                        push!(newsmtc,"(assert (precedeq a$(β.index) (join x$(string(cycle)) y$(string(cycle)))))")
                    elseif isa(β, FiniteTruth)
                        push!(newsmtc,"(assert (precedeq $(β.label) (join x$(string(cycle)) y$(string(cycle)))))")
                    else
                        error("Wrong truth type")
                    end
                    for l in leaves(en)                    
                        fta = HybridMVHSTableau{FiniteIndexTruth}(true, (x, a), en.interval, l.constraintsystem, l)
                        push!(metricheaps, fta)
                        ftb = HybridMVHSTableau{FiniteIndexTruth}(true, (y, b), en.interval, fta.constraintsystem, fta, newsmtc)
                        push!(metricheaps, ftb)
                    end       
                elseif !en.judgement && token(φ) isa NamedConnective{:∨} && !isbot(β)
                    # F(t→(A∨B)) case
                    (a, b) = children(φ)
                    x, y = FiniteTruth.(["x$(string(cycle))", "y$(string(cycle))"])
                    xsmtc = "(assert (or"
                    ysmtc = "(assert (or"
                    for value in 1:N
                        xsmtc *= " (= x$(string(cycle)) a$(string(value)))"
                        ysmtc *= " (= y$(string(cycle)) a$(string(value)))"
                    end
                    xsmtc *= "))\n"
                    ysmtc *= "))\n"
                    newsmtc = [
                        "(declare-const x$(string(cycle)) A1)",
                        "(declare-const y$(string(cycle)) A1)",
                        xsmtc,
                        ysmtc                    
                    ]
                    if isa(β, FiniteIndexTruth)
                        push!(newsmtc,"(assert (not (precedeq a$(β.index) (join x$(string(cycle)) y$(string(cycle))))))")
                    elseif isa(β, FiniteTruth)
                        push!(newsmtc,"(assert (not (precedeq $(β.label) (join x$(string(cycle)) y$(string(cycle))))))")
                    else
                        error("Wrong truth type")
                    end
                    for l in leaves(en)                    
                        fta = HybridMVHSTableau{FiniteIndexTruth}(true, (a, x), en.interval, l.constraintsystem, l)
                        push!(metricheaps, fta)
                        ftb = HybridMVHSTableau{FiniteIndexTruth}(true, (b, y), en.interval, fta.constraintsystem, fta, newsmtc)
                        push!(metricheaps, ftb)
                    end   
                # Implication Rules 1
                elseif en.judgement && token(φ) isa NamedConnective{:→} && !isbot(β)
                    # T(t→(A→B)) case
                    (a, b) = children(φ)
                    x, y = FiniteTruth.(["x$(string(cycle))", "y$(string(cycle))"])
                    xsmtc = "(assert (or"
                    ysmtc = "(assert (or"
                    for value in 1:N
                        xsmtc *= " (= x$(string(cycle)) a$(string(value)))"
                        ysmtc *= " (= y$(string(cycle)) a$(string(value)))"
                    end
                    xsmtc *= "))\n"
                    ysmtc *= "))\n"
                    newsmtc = [
                        "(declare-const x$(string(cycle)) A1)",
                        "(declare-const y$(string(cycle)) A1)",
                        xsmtc,
                        ysmtc                    
                    ]
                    if isa(β, FiniteIndexTruth)
                        push!(newsmtc,"(assert (precedeq a$(β.index) (implication x$(string(cycle)) y$(string(cycle)))))")
                    elseif isa(β, FiniteTruth)
                        push!(newsmtc,"(assert (precedeq $(β.label) (implication x$(string(cycle)) y$(string(cycle)))))")
                    else
                        error("Wrong truth type")
                    end
                    for l in leaves(en)                    
                        fta = HybridMVHSTableau{FiniteIndexTruth}(true, (a, x), en.interval, l.constraintsystem, l)
                        push!(metricheaps, fta)
                        ftb = HybridMVHSTableau{FiniteIndexTruth}(true, (y, b), en.interval, fta.constraintsystem, fta, newsmtc)
                        push!(metricheaps, ftb)
                    end       
                elseif !en.judgement && token(φ) isa NamedConnective{:→} && !isbot(β)
                    # F(t→(A→B)) case
                    (a, b) = children(φ)
                    x, y = FiniteTruth.(["x$(string(cycle))", "y$(string(cycle))"])
                    xsmtc = "(assert (or"
                    ysmtc = "(assert (or"
                    for value in 1:N
                        xsmtc *= " (= x$(string(cycle)) a$(string(value)))"
                        ysmtc *= " (= y$(string(cycle)) a$(string(value)))"
                    end
                    xsmtc *= "))\n"
                    ysmtc *= "))\n"
                    newsmtc = [
                        "(declare-const x$(string(cycle)) A1)",
                        "(declare-const y$(string(cycle)) A1)",
                        xsmtc,
                        ysmtc                    
                    ]
                    if isa(β, FiniteIndexTruth)
                        push!(newsmtc,"(assert (not (precedeq a$(β.index) (implication x$(string(cycle)) y$(string(cycle))))))")
                    elseif isa(β, FiniteTruth)
                        push!(newsmtc,"(assert (not (precedeq $(β.label) (implication x$(string(cycle)) y$(string(cycle))))))")
                    else
                        error("Wrong truth type")
                    end
                    for l in leaves(en)                    
                        fta = HybridMVHSTableau{FiniteIndexTruth}(true, (x, a), en.interval, l.constraintsystem, l)
                        push!(metricheaps, fta)
                        ftb = HybridMVHSTableau{FiniteIndexTruth}(true, (b, y), en.interval, fta.constraintsystem, fta, newsmtc)
                        push!(metricheaps, ftb)
                    end

                elseif en.judgement && token(φ) isa BoxRelationalConnective && !isbot(β)
                    # T□"
                    verbose && println("T□")
                    ψ = children(φ)[1]
                    for l ∈ findleaves(en)
                        r = SoleLogics.relation(token(φ))
                        (x, y) = en.interval
                        cB = l.constraintsystem
                        tj = l
                        for i ∈ eachindex(cB)
                            for j ∈ i+1:length(cB)
                                # declare new const for γi = R([x,y,zi,ti])
                                xi = FiniteTruth("x$(string(cycle))-$(string(i))-$(string(j))")
                                yi = FiniteTruth("y$(string(cycle))-$(string(i))-$(string(j))")
                                ysmtc = "(declare-const $(yi.label) A1)\n"
                                ysmtc *= "(assert (= $(yi.label) $(mveval(r,(x,y),(cB[i],cB[j])))))\n"
                                xsmtc = "(declare-const $(xi.label) A1)\n"
                                xsmtc *= "(assert (or"
                                ysmtc *= "(assert (or"
                                for value in 1:N
                                    xsmtc *= " (= $(xi.label) a$(string(value)))"
                                    ysmtc *= " (= $(yi.label) a$(string(value)))"
                                end
                                xsmtc *= "))\n"
                                ysmtc *= "))\n"
                                if isa(β, FiniteIndexTruth)
                                    xsmtc *= "(assert (= $(xi.label) (meet a$(β.index) $(yi.label))))\n"
                                elseif isa(β, FiniteTruth)
                                    xsmtc *= "(assert (= $(xi.label) (meet $(β.label) $(yi.label))))\n"
                                else
                                    error("Wrong truth type")
                                end
                                xsmtc *= "(assert (distinct $(mveval(r,(x,y),(cB[i],cB[j]))) a2))\n"  # R([x,y],[zi,ti]) ≻ 0
                                tj = HybridMVHSTableau{FiniteIndexTruth}(
                                    true,
                                    (xi,ψ),
                                    (cB[i],cB[j]),
                                    cB,
                                    tj,
                                    [ysmtc, xsmtc]
                                )
                                push!(metricheaps, tj)  
                            end
                        end
                        if !findtableau(l,true,l.boundingimplication,l.interval)    # TODO: check
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
                            collect(Iterators.product((getdomain(algebra) for p ∈ cB0.domain)...)),
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
                                            if !isbot(βi) && !isbot(algebra.meet(β, βi))
                                                Threads.lock(u) do
                                                    tj = HybridMVHSTableau{FiniteIndexTruth}(
                                                        false,
                                                        (algebra.meet(βi, β), φ.children[1]),
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
                                            if !isbot(βi) && !isbot(algebra.meet(β, βi))
                                                Threads.lock(u) do
                                                    tj = HybridMVHSTableau{FiniteIndexTruth}(
                                                        false,
                                                        (algebra.meet(βi, β), φ.children[1]),
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
                                            collect(Iterators.product((getdomain(algebra) for p ∈ cB1.domain)...)),
                                            (1,:)
                                        )
                                            for gttcombs ∈ reshape(
                                                collect(Iterators.product((getdomain(algebra) for p ∈ cB1.domain)...)),
                                                (1,:)
                                            )
                                                for eqtcombs ∈ reshape(
                                                    collect(Iterators.product((getdomain(algebra) for p ∈ cB1.domain)...)),
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
                                                            if !isbot(βi) && !isbot(algebra.meet(β, βi))
                                                                Threads.lock(u) do
                                                                    tj = HybridMVHSTableau{FiniteIndexTruth}(
                                                                        false,
                                                                        (algebra.meet(βi, β), φ.children[1]),
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
                                                            if !isbot(βi) && !isbot(algebra.meet(β, βi))
                                                                Threads.lock(u) do
                                                                    tj = HybridMVHSTableau{FiniteIndexTruth}(
                                                                        false,
                                                                        (algebra.meet(βi, β), φ.children[1]),
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
                # elseif en.judgement && !isbot(β)
                #     # T⪰
                #     verbose && println("T⪰")
                #     for l ∈ findleaves(en)
                #         ti = l
                #         newnodes = false
                #         for γ in maximalmembers(a, β)
                #             if !findtableau(ti, false, (φ, γ), en.interval)
                #                 newnodes = true
                #                 ti = HybridMVHSTableau{FiniteIndexTruth}(
                #                     false,
                #                     (φ, γ),
                #                     en.interval,
                #                     l.constraintsystem,
                #                     ti
                #                 )
                #                 push!(metricheaps, ti)
                #             end
                #         end
                #         !newnodes && l == node && push!(metricheaps, node)
                #     end
                # elseif !en.judgement && !isbot(β)
                #     # F⪰
                #     verbose && println("F⪰")
                #     for l ∈ findleaves(en)
                #         newnodes = false
                #         for βi in maximalmembers(a, β)
                #             newnodes = true
                #             if !findtableau(l, true, (φ, βi), en.interval)
                #                 ti = HybridMVHSTableau{FiniteIndexTruth}(
                #                     true,
                #                     (φ, βi),
                #                     en.interval,
                #                     l.constraintsystem,
                #                     l
                #                 )
                #                 push!(metricheaps, ti)
                #             else  # Here there should be a branch and I need to keep track of it
                #                 ti = HybridMVHSTableau{FiniteIndexTruth}(   # Fake node (always true)
                #                     true,
                #                     (FiniteIndexTruth(1), FiniteIndexTruth(1)),
                #                     en.interval,
                #                     l.constraintsystem,
                #                     l
                #                 )
                #                 push!(metricheaps, ti)
                #             end
                #         end
                #         !newnodes && l == node && push!(metricheaps, node)
                #     end
                # Error
                elseif !isa(φ, Atom) && token(β) ∉ [∧, ∨, →]
                    error("Unrecognized operator $(token(φ)).")
                # Base case
                else
                    # No condition matched, pushing node back into metricheaps
                    push!(metricheaps, node)
                end
            elseif en.boundingimplication isa Tuple{Formula, Truth}
                φ = en.boundingimplication[1]
                β = en.boundingimplication[2]
                # Branch Closure Conditions
                if !en.judgement && istop(β)
                    # X4
                    verbose && println("X4")
                    close!(en)
                elseif findsimilar(en, algebra)
                    close!(en)
               # Strong conjunction Rules 2
            elseif en.judgement && token(φ) isa NamedConnective{:∧} && !istop(β)
                # T((A∧B)→t) case
                (a, b) = children(φ)
                x, y = FiniteTruth.(["x$(string(cycle))", "y$(string(cycle))"])
                xsmtc = "(assert (or"
                ysmtc = "(assert (or"
                for value in 1:N
                    xsmtc *= " (= x$(string(cycle)) a$(string(value)))"
                    ysmtc *= " (= y$(string(cycle)) a$(string(value)))"
                end
                xsmtc *= "))"
                ysmtc *= "))"
                newsmtc = [
                    "(declare-const x$(string(cycle)) A1)",
                    "(declare-const y$(string(cycle)) A1)",
                    xsmtc,
                    ysmtc                
                ]
                if isa(β, FiniteIndexTruth)
                    push!(newsmtc,"(assert (precedeq (monoid x$(string(cycle)) y$(string(cycle))) a$(β.index)))")
                elseif isa(β, FiniteTruth)
                    push!(newsmtc,"(assert (precedeq (monoid x$(string(cycle)) y$(string(cycle))) $(β.label)))")
                else
                    error("Wrong truth type")
                end
                for l in leaves(en)                    
                    fta = HybridTableau(SignedFormula(true, (a, x)), l)
                    push!(metricheaps, fta)
                    ftb = HybridTableau(SignedFormula(true, (b, y)), fta, newsmtc)
                    push!(metricheaps, ftb)
                end                
            elseif !en.judgement && token(φ) isa NamedConnective{:∧} && !istop(β)
                # F((A∧B)→t) case
                (a, b) = children(φ)
                x, y = FiniteTruth.(["x$(string(cycle))", "y$(string(cycle))"])
                xsmtc = "(assert (or"
                ysmtc = "(assert (or"
                for value in 1:N
                    xsmtc *= " (= x$(string(cycle)) a$(string(value)))"
                    ysmtc *= " (= y$(string(cycle)) a$(string(value)))"
                end
                xsmtc *= "))"
                ysmtc *= "))"
                newsmtc = [
                    "(declare-const x$(string(cycle)) A1)",
                    "(declare-const y$(string(cycle)) A1)",
                    xsmtc,
                    ysmtc                
                ]
                if isa(β, FiniteIndexTruth)
                    push!(newsmtc,"(assert (not (precedeq (monoid x$(string(cycle)) y$(string(cycle))) a$(β.index))))")
                elseif isa(β, FiniteTruth)
                    push!(newsmtc,"(assert (not (precedeq (monoid x$(string(cycle)) y$(string(cycle))) $(β.label))))")
                else
                    error("Wrong truth type")
                end
                for l in leaves(en)                    
                    fta = HybridTableau(SignedFormula(true, (x, a)), l)
                    push!(metricheaps, fta)
                    ftb = HybridTableau(SignedFormula(true, (y, b)), fta, newsmtc)
                    push!(metricheaps, ftb)
                end         
            # Strong disjunction rules 1
            elseif en.judgement && token(φ) isa NamedConnective{:∨} && !istop(β)
                # T((A∨B)→t) case
                (a, b) = children(φ)
                x, y = FiniteTruth.(["x$(string(cycle))", "y$(string(cycle))"])
                xsmtc = "(assert (or"
                ysmtc = "(assert (or"
                for value in 1:N
                    xsmtc *= " (= x$(string(cycle)) a$(string(value)))"
                    ysmtc *= " (= y$(string(cycle)) a$(string(value)))"
                end
                xsmtc *= "))"
                ysmtc *= "))"
                newsmtc = [
                    "(declare-const x$(string(cycle)) A1)",
                    "(declare-const y$(string(cycle)) A1)",
                    xsmtc,
                    ysmtc                    
                ]
                if isa(β, FiniteIndexTruth)
                    push!(newsmtc,"(assert (precedeq (join x$(string(cycle)) y$(string(cycle))) a$(β.index)))")
                elseif isa(β, FiniteTruth)
                    push!(newsmtc,"(assert (precedeq (join x$(string(cycle)) y$(string(cycle))) $(β.label)))")
                else
                    error("Wrong truth type")
                end
                for l in leaves(en)                    
                    fta = HybridTableau(SignedFormula(true, (a, x)), l)
                    push!(metricheaps, fta)
                    ftb = HybridTableau(SignedFormula(true, (b, y)), fta, newsmtc)
                    push!(metricheaps, ftb)
                end       
            elseif !en.judgement && token(φ) isa NamedConnective{:∨} && !istop(β)
                # F((A∨B)→t) case
                (a, b) = children(φ)
                x, y = FiniteTruth.(["x$(string(cycle))", "y$(string(cycle))"])
                xsmtc = "(assert (or"
                ysmtc = "(assert (or"
                for value in 1:N
                    xsmtc *= " (= x$(string(cycle)) a$(string(value)))"
                    ysmtc *= " (= y$(string(cycle)) a$(string(value)))"
                end
                xsmtc *= "))"
                ysmtc *= "))"
                newsmtc = [
                    "(declare-const x$(string(cycle)) A1)",
                    "(declare-const y$(string(cycle)) A1)",
                    xsmtc,
                    ysmtc                    
                ]
                if isa(β, FiniteIndexTruth)
                    push!(newsmtc,"(assert (not (precedeq (join x$(string(cycle)) y$(string(cycle))) a$(β.index))))")
                elseif isa(β, FiniteTruth)
                    push!(newsmtc,"(assert (not (precedeq (join x$(string(cycle)) y$(string(cycle))) $(β.label))))")
                else
                    error("Wrong truth type")
                end
                for l in leaves(en)                    
                    fta = HybridTableau(SignedFormula(true, (x, a)), l)
                    push!(metricheaps, fta)
                    ftb = HybridTableau(SignedFormula(true, (y, b)), fta, newsmtc)
                    push!(metricheaps, ftb)
                end    
            # Implication Rules 2
            elseif en.judgement && token(φ) isa NamedConnective{:→} && !istop(β)
                # T((A→B)→t) case
                (a, b) = children(φ)
                x, y = FiniteTruth.(["x$(string(cycle))", "y$(string(cycle))"])
                xsmtc = "(assert (or"
                ysmtc = "(assert (or"
                for value in 1:N
                    xsmtc *= " (= x$(string(cycle)) a$(string(value)))"
                    ysmtc *= " (= y$(string(cycle)) a$(string(value)))"
                end
                xsmtc *= "))"
                ysmtc *= "))"
                newsmtc = [
                    "(declare-const x$(string(cycle)) A1)",
                    "(declare-const y$(string(cycle)) A1)",
                    xsmtc,
                    ysmtc                    
                ]
                if isa(β, FiniteIndexTruth)
                    push!(newsmtc,"(assert (precedeq (implication x$(string(cycle)) y$(string(cycle))) a$(β.index)))")
                elseif isa(β, FiniteTruth)
                    push!(newsmtc,"(assert (precedeq (implication x$(string(cycle)) y$(string(cycle))) $(β.label)))")
                else
                    error("Wrong truth type")
                end
                for l in leaves(en)                    
                    fta = HybridTableau(SignedFormula(true, (x, a)), l)
                    push!(metricheaps, fta)
                    ftb = HybridTableau(SignedFormula(true, (b, y)), fta, newsmtc)
                    push!(metricheaps, ftb)
                end       
            elseif !en.judgement && token(φ) isa NamedConnective{:→} && !istop(β)
                # F((A→B)→t) case
                (a, b) = children(φ)
                x, y = FiniteTruth.(["x$(string(cycle))", "y$(string(cycle))"])
                xsmtc = "(assert (or"
                ysmtc = "(assert (or"
                for value in 1:N
                    xsmtc *= " (= x$(string(cycle)) a$(string(value)))"
                    ysmtc *= " (= y$(string(cycle)) a$(string(value)))"
                end
                xsmtc *= "))"
                ysmtc *= "))"
                newsmtc = [
                    "(declare-const x$(string(cycle)) A1)",
                    "(declare-const y$(string(cycle)) A1)",
                    xsmtc,
                    ysmtc                    
                ]
                if isa(β, FiniteIndexTruth)
                    push!(newsmtc,"(assert (not (precedeq (implication x$(string(cycle)) y$(string(cycle))) a$(β.index))))")
                elseif isa(β, FiniteTruth)
                    push!(newsmtc,"(assert (not (precedeq (implication x$(string(cycle)) y$(string(cycle))) $(β.label))))")
                else
                    error("Wrong truth type")
                end
                for l in leaves(en)                    
                    fta = HybridTableau(SignedFormula(true, (a, x)), l)
                    push!(metricheaps, fta)
                    ftb = HybridTableau(SignedFormula(true, (y, b)), fta, newsmtc)
                    push!(metricheaps, ftb)
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
                                if !istop(βi) && !istop(algebra.implication(βi, β))
                                    # Optimization 1 (int. node)
                                    if !findtableau(tj,true,(φ.children[1], algebra.implication(βi, β)),Interval(zi,ti))
                                        tj = HybridMVHSTableau{FiniteIndexTruth}(
                                            true,
                                            (φ.children[1], algebra.implication(βi, β)),
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
                                if !istop(βi) && !istop(algebra.implication(βi, β))
                                    tj = HybridMVHSTableau{FiniteIndexTruth}(
                                        false,
                                        (φ.children[1], algebra.implication(βi, β)),
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
                            collect(Iterators.product((getdomain(algebra) for p ∈ cB0.domain)...)),
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
                                            if !istop(βi) && !istop(algebra.implication(βi, β))
                                                Threads.lock(u) do
                                                    tj = HybridMVHSTableau{FiniteIndexTruth}(
                                                        false,
                                                        (φ.children[1], algebra.implication(βi, β)),
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
                                            if !istop(βi) && !istop(algebra.implication(βi, β))
                                                Threads.lock(u) do
                                                    tj = HybridMVHSTableau{FiniteIndexTruth}(
                                                        false,
                                                        (φ.children[1], algebra.implication(βi, β)),
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
                                            collect(Iterators.product((getdomain(algebra) for p ∈ cB1.domain)...)),
                                            (1,:)
                                        )
                                            for gttcombs ∈ reshape(
                                                collect(Iterators.product((getdomain(algebra) for p ∈ cB1.domain)...)),
                                                (1,:)
                                            )
                                                for eqtcombs ∈ reshape(
                                                    collect(Iterators.product((getdomain(algebra) for p ∈ cB1.domain)...)),
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
                                                            if !istop(βi) && !istop(algebra.implication(βi, β))
                                                                Threads.lock(u) do
                                                                    tj = HybridMVHSTableau{FiniteIndexTruth}(
                                                                        false,
                                                                        (φ.children[1], algebra.implication(βi, β)),
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
                                                            if !istop(βi) && !istop(algebra.implication(βi, β))
                                                                Threads.lock(u) do
                                                                    tj = HybridMVHSTableau{FiniteIndexTruth}(
                                                                        false,
                                                                        (φ.children[1], algebra.implication(βi, β)),
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
                # elseif en.judgement && !istop(β)
                #     # T⪯
                #     verbose && println("T⪯")
                #     for l ∈ findleaves(en)
                #         ti = l
                #         newnodes = false
                #         for γ in minimalmembers(a, β)
                #             if !findtableau(ti, false, (γ, φ), en.interval)
                #                 newnodes = true
                #                 ti = HybridMVHSTableau{FiniteIndexTruth}(
                #                     false,
                #                     (γ, φ),
                #                     en.interval,
                #                     l.constraintsystem,
                #                     ti
                #                 )
                #                 push!(metricheaps, ti)
                #             end
                #         end
                #         !newnodes && l == node && push!(metricheaps, node)
                #     end
                # elseif !en.judgement && !istop(β)
                #     # F⪯
                #     verbose && println("F⪯")
                #     for l ∈ findleaves(en)
                #         newnodes = false
                #         for βi in minimalmembers(a, β)
                #             newnodes = true
                #             if !findtableau(l, true, (βi, φ), en.interval)
                #                 ti = HybridMVHSTableau{FiniteIndexTruth}(
                #                     true,
                #                     (βi, φ),
                #                     en.interval,
                #                     l.constraintsystem,
                #                     l
                #                 )
                #                 push!(metricheaps, ti)
                #             else  # Here there should be a branch and I need to keep track of it
                #                 ti = HybridMVHSTableau{FiniteIndexTruth}(   # Fake node (always true)
                #                     true,
                #                     (FiniteIndexTruth(1), FiniteIndexTruth(1)),
                #                     en.interval,
                #                     l.constraintsystem,
                #                     l
                #                 )
                #                 push!(metricheaps, ti)
                #             end
                #         end
                #         !newnodes && l == node && push!(metricheaps, node)
                #     end
                # Error
                elseif !isa(φ, Atom) && token(z[1]) ∉ [∧, ∨, →]
                    error("Unrecognized operator $(token(φ)).")
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
    p1, p2 = Point.(["p1", "p2"])
    constraintsystem = [p1, p2]
    newsmtc = ""
    newsmtc *= "(declare-const p1 A2)\n(declare-const p2 A2)\n"
    newsmtc *= "(assert (distinct (mvlt p1 p2) a2))\n"
    tableau = HybridMVHSTableau{FiniteIndexTruth}(
        true,
        (α, φ),
        (p1, p2),
        constraintsystem,
        [newsmtc]
    )
    metricheaps = Vector{MetricHeap}()   # Heaps to be used for node selection
    for metric ∈ metrics
        push!(metricheaps, MetricHeap(metric))
    end
    for metricheap ∈ metricheaps
        push!(heap(metricheap), MetricHeapNode(metric(metricheap), tableau))
    end
    r = hybridmvhsalphasat(metricheaps, choosenode, a; verbose, timeout, diamondexpansion)
    
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
