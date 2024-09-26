using SoleLogics: AbstractAlgebra
using SoleLogics.ManyValuedLogics: FiniteIndexAlgebra, FiniteIndexFLewAlgebra, FiniteIndexTruth

"""
    struct SignedFormula{T<:Truth}
        sign::Bool
        boundingimplication::Union{Tuple{T, Formula}, Tuple{Formula, T}, Tuple{T, T}}
    end

All formulas appearing in the many-valued tableau will be bounding implications, i.e.,
a → A (or A → a), where a is a propositional constant and asserting a ≤ A (resp. A ≤ a).
"""
struct SignedFormula{T<:Truth}
    sign::Bool
    boundingimplication::Union{Tuple{T, Formula}, Tuple{Formula, T}, Tuple{T, T}}
    
    function SignedFormula(
        sign::Bool,
        boundingimplication::Union{Tuple{T, Formula}, Tuple{Formula, T}, Tuple{T, T}}
    ) where {
        T<:Truth
    }
        return new{T}(sign, boundingimplication)
    end
end

function Base.show(io::IO, sz::SignedFormula)
    print(
        io,
        "$(string(sz.sign))("*
        "( $(syntaxstring(sz.boundingimplication[1], remove_redundant_parentheses=false)) )"*
        " ⪯ "*
        "( $(syntaxstring(sz.boundingimplication[2], remove_redundant_parentheses=false))) )"*
        ")"
    )
end

function Base.convert(
    ::Type{SignedFormula{T1}},
    sz::SignedFormula{T2}
) where {
    T1<:Truth,
    T2<:Truth
}
    if sz.boundingimplication isa Tuple{T2, Formula}
        return SignedFormula(
            sz.sign,
            (convert(T1, sz.boundingimplication[1]), sz.boundingimplication[2])
        )
    elseif sz.boundingimplication isa Tuple{Formula, T2}
        return SignedFormula(
            sz.sign,
            (sz.boundingimplication[1], convert(T1, sz.boundingimplication[2]))
        )
    elseif sz.boundingimplication isa Tuple{T2, T2}
        return SignedFormula(
            sz.sign,
            (convert(T1, sz.boundingimplication[1]), convert(T1, sz.boundingimplication[2]))
        )
    elseif sz.boundingimplication isa Tuple{T1, T2}
        return SignedFormula(
            sz.sign,
            (sz.boundingimplication[1], convert(T1, sz.boundingimplication[2]))
        )
    elseif sz.boundingimplication isa Tuple{T2, T1}
        return SignedFormula(
            sz.sign,
            (convert(T1, sz.boundingimplication[1]), sz.boundingimplication[2])
        )
    else
        error(
            "Cannot convert object of type $(typeof(sz)) to a value of type "*
            "SignedFormula{$T2}"
        )
    end
end

"""
    mutable struct ManyValuedTableau{T<:Truth} <: AbstractTableau
        const signedformula::SignedFormula{T}
        const father::Union{ManyValuedTableau{T}, Nothing}
        children::Vector{ManyValuedTableau{T}}
        expanded::Bool
        closed::Bool
    end

A mutable structure representing a tableau as a tree structure, with each node containing
a signed formula, the father and children in the tree structure, a flag saying if the node
has already been expanded and a flag saying if the branch represented by the node has been
closed. Each path from a leaf to the root respresents a branch.
"""
mutable struct ManyValuedTableau{T<:Truth} <: AbstractTableau
    const signedformula::SignedFormula{T}
    const father::Union{ManyValuedTableau{T}, Nothing}
    children::Vector{ManyValuedTableau{T}}
    expanded::Bool
    closed::Bool

    function ManyValuedTableau(
        signedformula::SignedFormula{T},
        father::ManyValuedTableau{T},
        children::Vector{ManyValuedTableau{T}},
        expanded::Bool,
        closed::Bool
    ) where {
        T<:Truth
    }
        return new{T}(signedformula, father, children, expanded, closed)
    end

    function ManyValuedTableau(
        signedformula::SignedFormula{T},
        _::Nothing,
        children::Vector{ManyValuedTableau{T}},
        expanded::Bool,
        closed::Bool
    ) where {
        T<:Truth
    }
        return new{T}(signedformula, nothing, children, expanded, closed)
    end

    function ManyValuedTableau(
        signedformula::SignedFormula{T1},
        father::ManyValuedTableau{T}
    ) where {
        T1<:Truth,
        T<:Truth
    }
        if !isa(signedformula, SignedFormula{T})
            signedformula = convert(SignedFormula{T}, signedformula)::SignedFormula{T}
        end
        ft = ManyValuedTableau(
            signedformula,
            father,
            Vector{ManyValuedTableau{T}}(),
            false,
            false
        )
        pushchild!(father, ft)
        return ft
    end

    function ManyValuedTableau(signedformula::SignedFormula{T}) where {T<:Truth}
        return ManyValuedTableau(
            signedformula,
            nothing,
            Vector{ManyValuedTableau{T}}(),
            false,
            false
        )
    end
end

function Base.show(io::IO, t::ManyValuedTableau)
    b = []
    append!(b, [t.signedformula])
    while !isroot(t)
        t = t.father
        append!(b, [t.signedformula])
    end
    reverse!(b)
    println(io, "Satisfiable branch:")
    for sz in b
        println(io, string(sz))
    end
end

"""
Given a ManyValuedTableau containing a signed formula in the form T(b → X) or F(a → X),
return true if there is a tableau in the form F(a → X) (resp. T(b → X)) so that a ≤ b
in the given algebra in the same branch.
"""
function findsimilar(
    ft::ManyValuedTableau,
    h::A
) where {
    A<:AbstractAlgebra
}
    sz = ft.signedformula
    s = sz.sign
    z = sz.boundingimplication
    if z[1] isa Truth
        if s
            # Looking for F(a→X) where a≤b or T(X→a) where a<b
            while !isroot(ft)
                ft = ft.father
                sy = ft.signedformula
                y = sy.boundingimplication
                if y[1] isa Truth && !sy.sign && z[2] == y[2] && precedeq(h, y[1], z[1])
                    return true
                end
            end
        else
            # Looking for T(b→X) or where a≤b F(X→b) where a<b
            while !isroot(ft)
                ft = ft.father
                sy = ft.signedformula
                y = sy.boundingimplication
                if y[1] isa Truth && sy.sign && z[2] == y[2] && precedeq(h, z[1], y[1])
                    return true
                end
            end
        end
    end
    return false
end

"""
Given a ManyValuedTableau containing a signed formula, return true if there is already a
tableau in the same form in the same branch.
"""
function findformula(ft::ManyValuedTableau, sz::SignedFormula)
    sy = ft.signedformula
    sz == sy && return true
    while !isroot(ft)
        ft = ft.father
        sy = ft.signedformula
        sz == sy && return true
    end
    return false
end

function sat(
    metricheaps::Vector{MetricHeap},
    choosenode::Function,
    h::FiniteFLewAlgebra{T,D};
    verbose::Bool=false,
    timeout::Union{Nothing,Int}=nothing,
    kwargs...
) where {
    T<:Truth,
    D<:AbstractVector{T}
}
    cycle = 1
    t0 = time_ns()
    while true

        # every 1000 cycles, clean heaps to improve both time and space efficiency
        if cycle%1e3==0
            cleanheaps!(metricheaps)
        end

        # if timeout, return nothing with a warning
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
        if isexpanded(node) # found a satisfiable branch
            verbose && println(node) # print satisfiable branch
            return true
        end
        en = findexpansionnode(node)
        expand!(en)

        sz = en.signedformula
        if !isa(sz, SignedFormula{T})
            sz = convert(SignedFormula{T}, sz)::SignedFormula{T}
        end
        s = sz.sign
        z = sz.boundingimplication

        verbose && println(string(s) * "\t" * string(z))

        if z isa Tuple{Truth, Truth}
            # Branch Closure Conditions
            if s && !precedeq(h, z[1], z[2])
                # T(a→b) where a≰b case
                close!(en)
            elseif !s && precedeq(h, z[1], z[2]) && !isbot(z[1]) && !istop(z[2])
                # F(a→b) where a≤b and a≠⊥ and b≠⊤ case
                close!(en)
            elseif !s && isbot(z[1])
                # F(⊥→X) case
                close!(en)
            elseif !s && istop(z[2])
                # F(X→⊤) case
                close!(en)
            elseif findsimilar(en, h)
                # T(b→X) and F(a→X) where a ≤ b case
                close!(en)
            # Base case
            else
                # No condition matched, pushing node back into metricheaps
                push!(metricheaps, node)
            end
        elseif z isa Tuple{T, Formula}
            # Branch Closure Conditions
            if !s && isbot(z[1])
                # F(⊥→X) case
                close!(en)
            elseif findsimilar(en, h)
                # T(b→X) and F(a→X) where a ≤ b case
                close!(en)
            # Strong conjunction Rules
            elseif s && token(z[2]) isa NamedConnective{:∧} && !isbot(z[1])
                # T(t→(A∧B)) case
                (a, b) = children(z[2])
                # Search for support tuples
                pairs = Set{NTuple{2,T}}()
                for ti ∈ getdomain(h)
                    for si ∈ getdomain(h)
                        if precedeq(h, z[1], h.monoid(ti, si))
                            push!(pairs, (ti, si))
                        end
                    end
                end
                for p in pairs
                    for q in pairs
                        if precedeq(h, q[1], p[1]) && precedeq(h, q[2], p[2]) && p != q
                            delete!(pairs, p)
                        end
                    end
                end
                for l ∈ leaves(en)
                    newnodes = false
                    for pair in pairs
                        newnodes = true
                        sy = SignedFormula(true, (pair[1], a))
                        if !findformula(l, sy)
                            fta = ManyValuedTableau(sy, l)
                            push!(metricheaps, fta)
                            sy = SignedFormula(true, (pair[2], b))
                            if !findformula(fta, sy)
                                ftb = ManyValuedTableau(sy, fta)
                                push!(metricheaps, ftb)
                            end
                        else
                            sy = SignedFormula(true, (pair[2], b))
                            if !findformula(l, sy)
                                newnodes = true
                                ftb = ManyValuedTableau(sy, l)
                                push!(metricheaps, ftb)
                            else  # Here there should be a branch and I need to keep track of it
                                sy = SignedFormula(true, (⊤, ⊤))    # Fake node (always true)
                                fti = ManyValuedTableau(sy, l)
                                push!(metricheaps, fti)
                            end
                        end
                    end
                    !newnodes && l == node && push!(metricheaps, node)
                end

            elseif !s && token(z[2]) isa NamedConnective{:∧} && !isbot(z[1])
                # F(t→(A∧B)) case
                (a, b) = children(z[2])
                # Search for support tuples
                pairs = Set{NTuple{2,T}}()
                for ti ∈ getdomain(h)
                    for si ∈ getdomain(h)
                        if !precedeq(h, z[1], h.monoid(ti, si))
                            push!(pairs, (ti, si))
                        end
                    end
                end
                for p in pairs
                    for q in pairs
                        if precedeq(h, p[1], q[1]) && precedeq(h, p[2], q[2]) && p != q
                            delete!(pairs, p)
                        end
                    end
                end
                for l ∈ leaves(en)
                    newnodes = false
                    for pair in pairs
                        newnodes = true
                        sy = SignedFormula(true, (a, pair[1]))
                        if !findformula(l, sy)
                            fta = ManyValuedTableau(sy, l)
                            push!(metricheaps, fta)
                            sy = SignedFormula(true, (b, pair[2]))
                            if !findformula(fta, sy)
                                ftb = ManyValuedTableau(sy, fta)
                                push!(metricheaps, ftb)
                            end
                        else
                            sy = SignedFormula(true, (b, pair[2]))
                            if !findformula(l, sy)
                                newnodes = true
                                ftb = ManyValuedTableau(sy, l)
                                push!(metricheaps, ftb)
                            else  # Here there should be a branch and I need to keep track of it
                                sy = SignedFormula(true, (⊤, ⊤))    # Fake node (always true)
                                fti = ManyValuedTableau(sy, l)
                                push!(metricheaps, fti)
                            end
                        end
                    end
                    !newnodes && l == node && push!(metricheaps, node)
                end
            # Implication Rules
            elseif !s && token(z[2]) isa NamedConnective{:→} && !isbot(z[1])
                # F(t→(A→B)) case
                (a, b) = children(z[2])
                # Search for support tuples
                pairs = Set{NTuple{2,T}}()
                for ti ∈ getdomain(h)
                    for si ∈ getdomain(h)
                        if !precedeq(h, z[1], h.implication(ti, si))
                            push!(pairs, (ti, si))
                        end
                    end
                end
                for p in pairs
                    for q in pairs
                        if precedeq(h, q[1], p[1]) && precedeq(h, p[2], q[2]) && p != q
                            delete!(pairs, p)
                        end
                    end
                end
                for l ∈ leaves(en)
                    newnodes = false
                    for pair in pairs
                        newnodes = true
                        sy = SignedFormula(true, (pair[1], a))
                        if !findformula(l, sy)
                            fta = ManyValuedTableau(sy, l)
                            push!(metricheaps, fta)
                            sy = SignedFormula(true, (b, pair[2]))
                            if !findformula(fta, sy)
                                ftb = ManyValuedTableau(sy, fta)
                                push!(metricheaps, ftb)
                            end
                        else
                            sy = SignedFormula(true, (b, pair[2]))
                            if !findformula(l, sy)
                                newnodes = true
                                ftb = ManyValuedTableau(sy, l)
                                push!(metricheaps, ftb)
                            else  # Here there should be a branch and I need to keep track of it
                                sy = SignedFormula(true, (⊤, ⊤))    # Fake node (always true)
                                fti = ManyValuedTableau(sy, l)
                                push!(metricheaps, fti)
                            end
                        end
                    end
                    !newnodes && l == node && push!(metricheaps, node)
                end
            elseif s && token(z[2]) isa NamedConnective{:→} && !isbot(z[1])
                # T(t→(A→B)) case
                (a, b) = children(z[2])
                # Search for support tuples
                pairs = Set{NTuple{2,T}}()
                for ti ∈ getdomain(h)
                    for si ∈ getdomain(h)
                        if precedeq(h, z[1], h.implication(ti, si))
                            push!(pairs, (ti, si))
                        end
                    end
                end
                for p in pairs
                    for q in pairs
                        if precedeq(h, p[1], q[1]) && precedeq(h, q[2], p[2]) && p != q
                            delete!(pairs, p)
                        end
                    end
                end
                for l ∈ leaves(en)
                    newnodes = false
                    for pair in pairs
                        newnodes = true
                        sy = SignedFormula(true, (a, pair[1]))
                        if !findformula(l, sy)
                            fta = ManyValuedTableau(sy, l)
                            push!(metricheaps, fta)
                            sy = SignedFormula(true, (pair[2], b))
                            if !findformula(fta, sy)
                                ftb = ManyValuedTableau(sy, fta)
                                push!(metricheaps, ftb)
                            end
                        else
                            sy = SignedFormula(true, (pair[2], b))
                            if !findformula(l, sy)
                                newnodes = true
                                ftb = ManyValuedTableau(sy, l)
                                push!(metricheaps, ftb)
                            else  # Here there should be a branch and I need to keep track of it
                                sy = SignedFormula(true, (⊤, ⊤))    # Fake node (always true)
                                fti = ManyValuedTableau(sy, l)
                                push!(metricheaps, fti)
                            end
                        end
                    end
                    !newnodes && l == node && push!(metricheaps, node)
                end
            # Reversal Rules
            elseif !s && !isbot(z[1])
                # F(a→X) case
                for l ∈ leaves(en)
                    newnodes = false
                    for ti ∈ maximalmembers(h, z[1])
                        newnodes = true
                        sy = SignedFormula(true, (z[2], ti))
                        if !findformula(l, sy)
                            newnodes = true
                            fti = ManyValuedTableau(sy, l)
                            push!(metricheaps, fti)
                        else  # Here there should be a branch and I need to keep track of it
                            sy = SignedFormula(true, (⊤, ⊤))    # Fake node (always true)
                            fti = ManyValuedTableau(sy, l)
                            push!(metricheaps, fti)
                        end
                    end
                    !newnodes && l == node && push!(metricheaps, node)
                end
            elseif s && !isbot(z[1])
                # T(a→X) case
                for l ∈ leaves(en)
                    newnodes = false
                    fti = l
                    for ti in maximalmembers(h, z[1])
                        sy = SignedFormula(false, (z[2], ti))
                        if !findformula(fti, sy)
                            newnodes = true
                            fti = ManyValuedTableau(sy, fti)
                            push!(metricheaps, fti)
                        end
                    end
                    !newnodes && l == node && push!(metricheaps, node)
                end
            # Error
            elseif !isa(z[2], Atom) && token(z[2]) ∉ [∧, ∨, →]
                error("Unrecognized operator $(token(z[2])).")
            # Base case
            else
                # No condition matched, pushing node back into metricheaps
                push!(metricheaps, node)
            end
        elseif z isa Tuple{Formula, T}
            # Branch Closure Conditions
            if !s && istop(z[2])
                # F(X→⊤) case
                close!(en)
            # Strong disjunction rules
            elseif s && token(z[1]) isa NamedConnective{:∨} && !istop(z[2])
                # T((A∨B)→t) case
                (a, b) = children(z[1])
                # Search for support tuples
                pairs = Set{NTuple{2,T}}()
                for ti ∈ getdomain(h)
                    for si ∈ getdomain(h)
                        if precedeq(h, h.join(ti, si), z[2])
                            push!(pairs, (ti, si))
                        end
                    end
                end
                for p in pairs
                    for q in pairs
                        if precedeq(h, p[1], q[1]) && precedeq(h, p[2], q[2]) && p != q
                            delete!(pairs, p)
                        end
                    end
                end
                for l ∈ leaves(en)
                    newnodes = false
                    for pair in pairs
                        newnodes = true
                        sy = SignedFormula(true, (a, pair[1]))
                        if !findformula(l, sy)
                            fta = ManyValuedTableau(sy, l)
                            push!(metricheaps, fta)
                            sy = SignedFormula(true, (b, pair[2]))
                            if !findformula(fta, sy)
                                ftb = ManyValuedTableau(sy, fta)
                                push!(metricheaps, ftb)
                            end
                        else
                            sy = SignedFormula(true, (b, pair[2]))
                            if !findformula(l, sy)
                                newnodes = true
                                ftb = ManyValuedTableau(sy, l)
                                push!(metricheaps, ftb)
                            else  # Here there should be a branch and I need to keep track of it
                                sy = SignedFormula(true, (⊤, ⊤))    # Fake node (always true)
                                fti = ManyValuedTableau(sy, l)
                                push!(metricheaps, fti)
                            end
                        end
                    end
                    !newnodes && l == node && push!(metricheaps, node)
                end
            elseif !s && token(z[1]) isa NamedConnective{:∨} && !istop(z[2])
                # F((A∨B)→t) case
                (a, b) = children(z[1])
                # Search for support tuples
                pairs = Set{NTuple{2,T}}()
                for ti ∈ getdomain(h)
                    for si ∈ getdomain(h)
                        if !precedeq(h, h.join(ti, si), z[2])
                            push!(pairs, (ti, si))
                        end
                    end
                end
                for p in pairs
                    for q in pairs
                        if precedeq(h, q[1], p[1]) && precedeq(h, q[2], p[2]) && p != q
                            delete!(pairs, p)
                        end
                    end
                end
                for l ∈ leaves(en)
                    newnodes = false
                    for pair in pairs
                        newnodes = true
                        sy = SignedFormula(true, (pair[1], a))
                        if !findformula(l, sy)
                            fta = ManyValuedTableau(sy, l)
                            push!(metricheaps, fta)
                            sy = SignedFormula(true, (pair[2], b))
                            if !findformula(fta, sy)
                                ftb = ManyValuedTableau(sy, fta)
                                push!(metricheaps, ftb)
                            end
                        else
                            sy = SignedFormula(true, (pair[2], b))
                            if !findformula(l, sy)
                                newnodes = true
                                ftb = ManyValuedTableau(sy, l)
                                push!(metricheaps, ftb)
                            else  # Here there should be a branch and I need to keep track of it
                                sy = SignedFormula(true, (⊤, ⊤))    # Fake node (always true)
                                fti = ManyValuedTableau(sy, l)
                                push!(metricheaps, fti)
                            end
                        end
                    end
                    !newnodes && l == node && push!(metricheaps, node)
                end
            # Reversal Rules
            elseif !s && !istop(z[2])
                # F(X→a) case
                for l ∈ leaves(en)
                    newnodes = false
                    for ui ∈ minimalmembers(h, z[2])
                        newnodes = true
                        sy = SignedFormula(true, (ui, z[1]))
                        if !findformula(l, sy)
                            fui = ManyValuedTableau(sy, l)
                            push!(metricheaps, fui)
                        else  # Here there should be a branch and I need to keep track of it
                            sy = SignedFormula(true, (⊤, ⊤))    # Fake node (always true)
                            fti = ManyValuedTableau(sy, l)
                            push!(metricheaps, fti)
                        end
                    end
                    !newnodes && l == node && push!(metricheaps, node)
                end
            elseif s && !istop(z[2])
                # T(X→A) case
                for l ∈ leaves(en)
                    newnodes = false
                    fui = l
                    for ui in minimalmembers(h, z[2])
                        sy = SignedFormula(false, (ui, z[1]))
                        if !findformula(fui, sy)
                            newnodes = true
                            fui = ManyValuedTableau(sy, fui)
                            push!(metricheaps, fui)
                        end
                    end
                    !newnodes && l == node && push!(metricheaps, node)
                end
            # Error
            elseif !isa(z[1], Atom) && token(z[1]) ∉ [∧, ∨, →]
                error("Unrecognized operator $(token(z[1])).")
            # Base case
            else
                # No condition matched, pushing node back into metricheaps
                push!(metricheaps, node)
            end
        else
            error("Something went wrong with tuple $(z) of type $(typeof(z))")
        end
        cycle += 1
    end
end

function sat(
    metricheaps::Vector{MetricHeap},
    choosenode::Function,
    h::FiniteHeytingAlgebra{T,D};
    oldrule::Bool=false,
    verbose::Bool=false,
    timeout::Union{Nothing,Int}=nothing,
    kwargs...
) where {
    T<:Truth,
    D<:AbstractVector{T}
}
    cycle = 1
    t0 = time_ns()
    while true

        if cycle%1e3==0
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
        if isexpanded(node) # found a satisfiable branch
            verbose && println(node) # print satisfiable branch
            return true
        end
        en = findexpansionnode(node)
        expand!(en)

        sz = en.signedformula
        if !isa(sz, SignedFormula{T})
            sz = convert(SignedFormula{T}, sz)::SignedFormula{T}
        end
        s = sz.sign
        z = sz.boundingimplication

        verbose && println(string(s) * "\t" * string(z))

        if z isa Tuple{Truth, Truth}
            # Branch Closure Conditions
            if s && !precedeq(h, z[1], z[2])
                # T(a→b) where a≰b case
                close!(en)
            elseif !s && precedeq(h, z[1], z[2]) && !isbot(z[1]) && !istop(z[2])
                # F(a→b) where a≤b and a≠⊥ and b≠⊤ case
                close!(en)
            elseif !s && isbot(z[1])
                # F(⊥→X) case
                close!(en)
            elseif !s && istop(z[2])
                # F(X→⊤) case
                close!(en)
            elseif findsimilar(en, h)
                # T(b→X) and F(a→X) where a ≤ b case
                close!(en)
            # Base case
            else
                # No condition matched, pushing node back into metricheaps
                push!(metricheaps, node)
            end
        elseif z isa Tuple{T, Formula}
            # Branch Closure Conditions
            if !s && isbot(z[1])
                # F(⊥→X) case
                close!(en)
            elseif findsimilar(en, h)
                # T(b→X) and F(a→X) where a ≤ b case
                close!(en)
            # Weak conjunction Rules
            elseif s && token(z[2]) isa NamedConnective{:∧} && !isbot(z[1])
                # T(t→(A∧B)) case
                (a, b) = children(z[2])
                for l ∈ leaves(en)
                    fta = ManyValuedTableau(SignedFormula(true, (z[1], a)), l)
                    push!(metricheaps, fta)
                    ftb = ManyValuedTableau(SignedFormula(true, (z[1], b)), fta)
                    push!(metricheaps, ftb)
                end
            elseif !s && token(z[2]) isa NamedConnective{:∧} && !isbot(z[1])
                # F(t→(A∧B)) case
                (a, b) = children(z[2])
                for l ∈ leaves(en)
                    fta = ManyValuedTableau(SignedFormula(false, (z[1], a)), l)
                    push!(metricheaps, fta)
                    ftb = ManyValuedTableau(SignedFormula(false, (z[1], b)), l)
                    push!(metricheaps, ftb)
                end
            # Implication rules
            elseif !s && token(z[2]) isa NamedConnective{:→} && !isbot(z[1])
                # F(t→(A→B)) case
                (a, b) = children(z[2])
                lvs = lesservalues(h, z[1])
                for l ∈ leaves(en)
                    newnodes = false
                    for ti ∈ lvs
                        if !isbot(ti)
                            newnodes = true
                            fta = ManyValuedTableau(SignedFormula(true, (ti, a)), l)
                            push!(metricheaps, fta)
                            ftb = ManyValuedTableau(SignedFormula(false, (ti, b)), fta)
                            push!(metricheaps, ftb)
                        end
                    end
                    !newnodes && l == node && push!(metricheaps, node)   
                end
            elseif s && token(z[2]) isa NamedConnective{:→} && !isbot(z[1])
                if oldrule
                    # (OLD) T(t→(A→B)) case
                    (a, b) = children(z[2])
                    lvs = lesservalues(h, z[1])
                    newnodes = false
                    for ti in lvs
                        if !isbot(ti)
                            for l ∈ leaves(en)
                                if l == node
                                    newnodes = true
                                end
                                fta = ManyValuedTableau(SignedFormula(false, (ti, a)), l)
                                push!(metricheaps, fta)
                                ftb = ManyValuedTableau(SignedFormula(true, (ti, b)), l)
                                push!(metricheaps, ftb)
                            end
                        end
                        !newnodes && push!(metricheaps, node)
                    end
                else
                    # (NEW) T(t→(A→B)) case
                    (a, b) = children(z[2])
                    # Search for support tuples
                    pairs = Set{NTuple{2,T}}()
                    for ti ∈ getdomain(h)
                        for si ∈ getdomain(h)
                            if precedeq(h, z[1], h.implication(ti, si))
                                push!(pairs, (ti, si))
                            end
                        end
                    end
                    for p in pairs
                        for q in pairs
                            if precedeq(h, p[1], q[1]) && precedeq(h, q[2], p[2]) && p != q
                                delete!(pairs, p)
                            end
                        end
                    end
                    for l ∈ leaves(en)
                        newnodes = false
                        for pair in pairs
                            newnodes = true
                            sy = SignedFormula(true, (a, pair[1]))
                            if !findformula(l, sy)
                                fta = ManyValuedTableau(sy, l)
                                push!(metricheaps, fta)
                                sy = SignedFormula(true, (pair[2], b))
                                if !findformula(fta, sy)
                                    ftb = ManyValuedTableau(sy, fta)
                                    push!(metricheaps, ftb)
                                end
                            else
                                sy = SignedFormula(true, (pair[2], b))
                                if !findformula(l, sy)
                                    newnodes = true
                                    ftb = ManyValuedTableau(sy, l)
                                    push!(metricheaps, ftb)
                                else  # Here there should be a branch and I need to keep track of it
                                    sy = SignedFormula(true, (⊤, ⊤))    # Fake node (always true)
                                    fti = ManyValuedTableau(sy, l)
                                    push!(metricheaps, fti)
                                end
                            end
                        end
                        !newnodes && l == node && push!(metricheaps, node)
                    end
                end
            # Reversal Rules
            elseif !s && !isbot(z[1])
                # F(a→X) case
                for l ∈ leaves(en)
                    newnodes = false
                    for ti ∈ maximalmembers(h, z[1])
                        newnodes = true
                        sy = SignedFormula(true, (z[2], ti))
                        if !findformula(l, sy)
                            newnodes = true
                            fti = ManyValuedTableau(sy, l)
                            push!(metricheaps, fti)
                        else  # Here there should be a branch and I need to keep track of it
                            sy = SignedFormula(true, (⊤, ⊤))    # Fake node (always true)
                            fti = ManyValuedTableau(sy, l)
                            push!(metricheaps, fti)
                        end
                    end
                    !newnodes && l == node && push!(metricheaps, node)
                end
            elseif s && !isbot(z[1])
                # T(a→X) case
                for l ∈ leaves(en)
                    newnodes = false
                    fti = l
                    for ti in maximalmembers(h, z[1])
                        sy = SignedFormula(false, (z[2], ti))
                        if !findformula(fti, sy)
                            newnodes = true
                            fti = ManyValuedTableau(sy, fti)
                            push!(metricheaps, fti)
                        end
                    end
                    !newnodes && l == node && push!(metricheaps, node)
                end
            # Error
            elseif !isa(z[2], Atom) && token(z[2]) ∉ [∧, ∨, →]
                error("Unrecognized operator $(token(z[2])).")
            # Base case
            else
                # No condition matched, pushing node back into metricheaps
                push!(metricheaps, node)
            end
        elseif z isa Tuple{Formula, T}
            # Branch Closure Conditions
            if !s && istop(z[2])
                # F(X→⊤) case
                close!(en)
            # Weak disjunction Rules
            elseif s && token(z[1]) isa NamedConnective{:∨} && !istop(z[2])
                # T((A∨B)→t) case
                (a, b) = children(z[1])
                for l ∈ leaves(en)
                    fta = ManyValuedTableau(SignedFormula(true, (a, z[2])), l)
                    push!(metricheaps, fta)
                    ftb = ManyValuedTableau(SignedFormula(true, (b, z[2])), fta)
                    push!(metricheaps, ftb)
                end
            elseif !s && token(z[1]) isa NamedConnective{:∨} && !istop(z[2])
                # F((A∨B)→t) case
                (a, b) = children(z[1])
                for l ∈ leaves(en)
                    fta = ManyValuedTableau(SignedFormula(false, (a, z[2])), l)
                    push!(metricheaps, fta)
                    ftb = ManyValuedTableau(SignedFormula(false, (b, z[2])), l)
                    push!(metricheaps, ftb)
                end
            # Reversal Rules
            elseif !s && !istop(z[2])
                # F(X→a) case
                for l ∈ leaves(en)
                    newnodes = false
                    for ui ∈ minimalmembers(h, z[2])
                        newnodes = true
                        sy = SignedFormula(true, (ui, z[1]))
                        if !findformula(l, sy)
                            fui = ManyValuedTableau(sy, l)
                            push!(metricheaps, fui)
                        else  # Here there should be a branch and I need to keep track of it
                            sy = SignedFormula(true, (⊤, ⊤))    # Fake node (always true)
                            fti = ManyValuedTableau(sy, l)
                            push!(metricheaps, fti)
                        end
                    end
                    !newnodes && l == node && push!(metricheaps, node)
                end
            elseif s && !istop(z[2])
                # T(X→A) case
                for l ∈ leaves(en)
                    newnodes = false
                    fui = l
                    for ui in minimalmembers(h, z[2])
                        sy = SignedFormula(false, (ui, z[1]))
                        if !findformula(fui, sy)
                            newnodes = true
                            fui = ManyValuedTableau(sy, fui)
                            push!(metricheaps, fui)
                        end
                    end
                    !newnodes && l == node && push!(metricheaps, node)
                end
            # Error
            elseif !isa(z[1], Atom) && token(z[1]) ∉ [∧, ∨, →]
                error("Unrecognized operator $(token(z[1])).")
            # Base case
            else
                # No condition matched, pushing node back into metricheaps
                push!(metricheaps, node)
            end
        else
            error("Something went wrong with tuple $(z) of type $(typeof(z))")
        end
        cycle += 1
    end
end

function sat(
    metricheaps::Vector{MetricHeap},
    choosenode::Function,
    h::FiniteIndexFLewAlgebra{N};
    verbose::Bool=false,
    timeout::Union{Nothing,Int}=nothing,
    kwargs...
) where {
    N
}
    cycle = 1
    t0 = time_ns()
    while true

        # every 1000 cycles, clean heaps to improve both time and space efficiency
        if cycle%1e3==0
            cleanheaps!(metricheaps)
        end

        # if timeout, return nothing with a warning
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
        if isexpanded(node) # found a satisfiable branch
            verbose && println(node) # print satisfiable branch
            return true
        end
        en = findexpansionnode(node)
        expand!(en)

        sz = en.signedformula
        if !isa(sz, SignedFormula{FiniteIndexTruth})
            sz = convert(SignedFormula{FiniteIndexTruth}, sz)::SignedFormula{FiniteIndexTruth}
        end
        s = sz.sign
        z = sz.boundingimplication

        verbose && println(string(s) * "\t" * string(z))

        if z isa Tuple{Truth, Truth}
            # Branch Closure Conditions
            if s && !precedeq(h, z[1], z[2])
                # T(a→b) where a≰b case
                close!(en)
            elseif !s && precedeq(h, z[1], z[2]) && !isbot(z[1]) && !istop(z[2])
                # F(a→b) where a≤b and a≠⊥ and b≠⊤ case
                close!(en)
            elseif !s && isbot(z[1])
                # F(⊥→X) case
                close!(en)
            elseif !s && istop(z[2])
                # F(X→⊤) case
                close!(en)
            elseif findsimilar(en, h)
                # T(b→X) and F(a→X) where a ≤ b case
                close!(en)
            # Base case
            else
                # No condition matched, pushing node back into metricheaps
                push!(metricheaps, node)
            end
        elseif z isa Tuple{FiniteIndexTruth, Formula}
            # Branch Closure Conditions
            if !s && isbot(z[1])
                # F(⊥→X) case
                close!(en)
            elseif findsimilar(en, h)
                # T(b→X) and F(a→X) where a ≤ b case
                close!(en)
            # Strong conjunction Rules
            elseif s && token(z[2]) isa NamedConnective{:∧} && !isbot(z[1])
                # T(t→(A∧B)) case
                (a, b) = children(z[2])
                # Search for support tuples
                pairs = Set{NTuple{2,FiniteIndexTruth}}()
                for ti ∈ getdomain(h)
                    for si ∈ getdomain(h)
                        if precedeq(h, z[1], h.monoid(ti, si))
                            push!(pairs, (ti, si))
                        end
                    end
                end
                for p in pairs
                    for q in pairs
                        if precedeq(h, q[1], p[1]) && precedeq(h, q[2], p[2]) && p != q
                            delete!(pairs, p)
                        end
                    end
                end
                for l ∈ leaves(en)
                    newnodes = false
                    for pair in pairs
                        newnodes = true
                        sy = SignedFormula(true, (pair[1], a))
                        if !findformula(l, sy)
                            fta = ManyValuedTableau(sy, l)
                            push!(metricheaps, fta)
                            sy = SignedFormula(true, (pair[2], b))
                            if !findformula(fta, sy)
                                ftb = ManyValuedTableau(sy, fta)
                                push!(metricheaps, ftb)
                            end
                        else
                            sy = SignedFormula(true, (pair[2], b))
                            if !findformula(l, sy)
                                newnodes = true
                                ftb = ManyValuedTableau(sy, l)
                                push!(metricheaps, ftb)
                            else  # Here there should be a branch and I need to keep track of it
                                sy = SignedFormula(true, (⊤, ⊤))    # Fake node (always true)
                                fti = ManyValuedTableau(sy, l)
                                push!(metricheaps, fti)
                            end
                        end
                    end
                    !newnodes && l == node && push!(metricheaps, node)
                end

            elseif !s && token(z[2]) isa NamedConnective{:∧} && !isbot(z[1])
                # F(t→(A∧B)) case
                (a, b) = children(z[2])
                # Search for support tuples
                pairs = Set{NTuple{2,FiniteIndexTruth}}()
                for ti ∈ getdomain(h)
                    for si ∈ getdomain(h)
                        if !precedeq(h, z[1], h.monoid(ti, si))
                            push!(pairs, (ti, si))
                        end
                    end
                end
                for p in pairs
                    for q in pairs
                        if precedeq(h, p[1], q[1]) && precedeq(h, p[2], q[2]) && p != q
                            delete!(pairs, p)
                        end
                    end
                end
                for l ∈ leaves(en)
                    newnodes = false
                    for pair in pairs
                        newnodes = true
                        sy = SignedFormula(true, (a, pair[1]))
                        if !findformula(l, sy)
                            fta = ManyValuedTableau(sy, l)
                            push!(metricheaps, fta)
                            sy = SignedFormula(true, (b, pair[2]))
                            if !findformula(fta, sy)
                                ftb = ManyValuedTableau(sy, fta)
                                push!(metricheaps, ftb)
                            end
                        else
                            sy = SignedFormula(true, (b, pair[2]))
                            if !findformula(l, sy)
                                newnodes = true
                                ftb = ManyValuedTableau(sy, l)
                                push!(metricheaps, ftb)
                            else  # Here there should be a branch and I need to keep track of it
                                sy = SignedFormula(true, (⊤, ⊤))    # Fake node (always true)
                                fti = ManyValuedTableau(sy, l)
                                push!(metricheaps, fti)
                            end
                        end
                    end
                    !newnodes && l == node && push!(metricheaps, node)
                end
            # Implication Rules
            elseif !s && token(z[2]) isa NamedConnective{:→} && !isbot(z[1])
                # F(t→(A→B)) case
                (a, b) = children(z[2])
                # Search for support tuples
                pairs = Set{NTuple{2,FiniteIndexTruth}}()
                for ti ∈ getdomain(h)
                    for si ∈ getdomain(h)
                        if !precedeq(h, z[1], h.implication(ti, si))
                            push!(pairs, (ti, si))
                        end
                    end
                end
                for p in pairs
                    for q in pairs
                        if precedeq(h, q[1], p[1]) && precedeq(h, p[2], q[2]) && p != q
                            delete!(pairs, p)
                        end
                    end
                end
                for l ∈ leaves(en)
                    newnodes = false
                    for pair in pairs
                        newnodes = true
                        sy = SignedFormula(true, (pair[1], a))
                        if !findformula(l, sy)
                            fta = ManyValuedTableau(sy, l)
                            push!(metricheaps, fta)
                            sy = SignedFormula(true, (b, pair[2]))
                            if !findformula(fta, sy)
                                ftb = ManyValuedTableau(sy, fta)
                                push!(metricheaps, ftb)
                            end
                        else
                            sy = SignedFormula(true, (b, pair[2]))
                            if !findformula(l, sy)
                                newnodes = true
                                ftb = ManyValuedTableau(sy, l)
                                push!(metricheaps, ftb)
                            else  # Here there should be a branch and I need to keep track of it
                                sy = SignedFormula(true, (⊤, ⊤))    # Fake node (always true)
                                fti = ManyValuedTableau(sy, l)
                                push!(metricheaps, fti)
                            end
                        end
                    end
                    !newnodes && l == node && push!(metricheaps, node)
                end
            elseif s && token(z[2]) isa NamedConnective{:→} && !isbot(z[1])
                # T(t→(A→B)) case
                (a, b) = children(z[2])
                # Search for support tuples
                pairs = Set{NTuple{2,FiniteIndexTruth}}()
                for ti ∈ getdomain(h)
                    for si ∈ getdomain(h)
                        if precedeq(h, z[1], h.implication(ti, si))
                            push!(pairs, (ti, si))
                        end
                    end
                end
                for p in pairs
                    for q in pairs
                        if precedeq(h, p[1], q[1]) && precedeq(h, q[2], p[2]) && p != q
                            delete!(pairs, p)
                        end
                    end
                end
                for l ∈ leaves(en)
                    newnodes = false
                    for pair in pairs
                        newnodes = true
                        sy = SignedFormula(true, (a, pair[1]))
                        if !findformula(l, sy)
                            fta = ManyValuedTableau(sy, l)
                            push!(metricheaps, fta)
                            sy = SignedFormula(true, (pair[2], b))
                            if !findformula(fta, sy)
                                ftb = ManyValuedTableau(sy, fta)
                                push!(metricheaps, ftb)
                            end
                        else
                            sy = SignedFormula(true, (pair[2], b))
                            if !findformula(l, sy)
                                newnodes = true
                                ftb = ManyValuedTableau(sy, l)
                                push!(metricheaps, ftb)
                            else  # Here there should be a branch and I need to keep track of it
                                sy = SignedFormula(true, (⊤, ⊤))    # Fake node (always true)
                                fti = ManyValuedTableau(sy, l)
                                push!(metricheaps, fti)
                            end
                        end
                    end
                    !newnodes && l == node && push!(metricheaps, node)
                end
            # Reversal Rules
            elseif !s && !isbot(z[1])
                # F(a→X) case
                for l ∈ leaves(en)
                    newnodes = false
                    for ti ∈ maximalmembers(h, z[1])
                        newnodes = true
                        sy = SignedFormula(true, (z[2], ti))
                        if !findformula(l, sy)
                            newnodes = true
                            fti = ManyValuedTableau(sy, l)
                            push!(metricheaps, fti)
                        else  # Here there should be a branch and I need to keep track of it
                            sy = SignedFormula(true, (⊤, ⊤))    # Fake node (always true)
                            fti = ManyValuedTableau(sy, l)
                            push!(metricheaps, fti)
                        end
                    end
                    !newnodes && l == node && push!(metricheaps, node)
                end
            elseif s && !isbot(z[1])
                # T(a→X) case
                for l ∈ leaves(en)
                    newnodes = false
                    fti = l
                    for ti in maximalmembers(h, z[1])
                        sy = SignedFormula(false, (z[2], ti))
                        if !findformula(fti, sy)
                            newnodes = true
                            fti = ManyValuedTableau(sy, fti)
                            push!(metricheaps, fti)
                        end
                    end
                    !newnodes && l == node && push!(metricheaps, node)
                end
            # Error
            elseif !isa(z[2], Atom) && token(z[2]) ∉ [∧, ∨, →]
                error("Unrecognized operator $(token(z[2])).")
            # Base case
            else
                # No condition matched, pushing node back into metricheaps
                push!(metricheaps, node)
            end
        elseif z isa Tuple{Formula, FiniteIndexTruth}
            # Branch Closure Conditions
            if !s && istop(z[2])
                # F(X→⊤) case
                close!(en)
            # Strong disjunction rules
            elseif s && token(z[1]) isa NamedConnective{:∨} && !istop(z[2])
                # T((A∨B)→t) case
                (a, b) = children(z[1])
                # Search for support tuples
                pairs = Set{NTuple{2,FiniteIndexTruth}}()
                for ti ∈ getdomain(h)
                    for si ∈ getdomain(h)
                        if precedeq(h, h.join(ti, si), z[2])
                            push!(pairs, (ti, si))
                        end
                    end
                end
                for p in pairs
                    for q in pairs
                        if precedeq(h, p[1], q[1]) && precedeq(h, p[2], q[2]) && p != q
                            delete!(pairs, p)
                        end
                    end
                end
                for l ∈ leaves(en)
                    newnodes = false
                    for pair in pairs
                        newnodes = true
                        sy = SignedFormula(true, (a, pair[1]))
                        if !findformula(l, sy)
                            fta = ManyValuedTableau(sy, l)
                            push!(metricheaps, fta)
                            sy = SignedFormula(true, (b, pair[2]))
                            if !findformula(fta, sy)
                                ftb = ManyValuedTableau(sy, fta)
                                push!(metricheaps, ftb)
                            end
                        else
                            sy = SignedFormula(true, (b, pair[2]))
                            if !findformula(l, sy)
                                newnodes = true
                                ftb = ManyValuedTableau(sy, l)
                                push!(metricheaps, ftb)
                            else  # Here there should be a branch and I need to keep track of it
                                sy = SignedFormula(true, (⊤, ⊤))    # Fake node (always true)
                                fti = ManyValuedTableau(sy, l)
                                push!(metricheaps, fti)
                            end
                        end
                    end
                    !newnodes && l == node && push!(metricheaps, node)
                end
            elseif !s && token(z[1]) isa NamedConnective{:∨} && !istop(z[2])
                # F((A∨B)→t) case
                (a, b) = children(z[1])
                # Search for support tuples
                pairs = Set{NTuple{2,FiniteIndexTruth}}()
                for ti ∈ getdomain(h)
                    for si ∈ getdomain(h)
                        if !precedeq(h, h.join(ti, si), z[2])
                            push!(pairs, (ti, si))
                        end
                    end
                end
                for p in pairs
                    for q in pairs
                        if precedeq(h, q[1], p[1]) && precedeq(h, q[2], p[2]) && p != q
                            delete!(pairs, p)
                        end
                    end
                end
                for l ∈ leaves(en)
                    newnodes = false
                    for pair in pairs
                        newnodes = true
                        sy = SignedFormula(true, (pair[1], a))
                        if !findformula(l, sy)
                            fta = ManyValuedTableau(sy, l)
                            push!(metricheaps, fta)
                            sy = SignedFormula(true, (pair[2], b))
                            if !findformula(fta, sy)
                                ftb = ManyValuedTableau(sy, fta)
                                push!(metricheaps, ftb)
                            end
                        else
                            sy = SignedFormula(true, (pair[2], b))
                            if !findformula(l, sy)
                                newnodes = true
                                ftb = ManyValuedTableau(sy, l)
                                push!(metricheaps, ftb)
                            else  # Here there should be a branch and I need to keep track of it
                                sy = SignedFormula(true, (⊤, ⊤))    # Fake node (always true)
                                fti = ManyValuedTableau(sy, l)
                                push!(metricheaps, fti)
                            end
                        end
                    end
                    !newnodes && l == node && push!(metricheaps, node)
                end
            # Reversal Rules
            elseif !s && !istop(z[2])
                # F(X→a) case
                for l ∈ leaves(en)
                    newnodes = false
                    for ui ∈ minimalmembers(h, z[2])
                        newnodes = true
                        sy = SignedFormula(true, (ui, z[1]))
                        if !findformula(l, sy)
                            fui = ManyValuedTableau(sy, l)
                            push!(metricheaps, fui)
                        else  # Here there should be a branch and I need to keep track of it
                            sy = SignedFormula(true, (⊤, ⊤))    # Fake node (always true)
                            fti = ManyValuedTableau(sy, l)
                            push!(metricheaps, fti)
                        end
                    end
                    !newnodes && l == node && push!(metricheaps, node)
                end
            elseif s && !istop(z[2])
                # T(X→A) case
                for l ∈ leaves(en)
                    newnodes = false
                    fui = l
                    for ui in minimalmembers(h, z[2])
                        sy = SignedFormula(false, (ui, z[1]))
                        if !findformula(fui, sy)
                            newnodes = true
                            fui = ManyValuedTableau(sy, fui)
                            push!(metricheaps, fui)
                        end
                    end
                    !newnodes && l == node && push!(metricheaps, node)
                end
            # Error
            elseif !isa(z[1], Atom) && token(z[1]) ∉ [∧, ∨, →]
                error("Unrecognized operator $(token(z[1])).")
            # Base case
            else
                # No condition matched, pushing node back into metricheaps
                push!(metricheaps, node)
            end
        else
            error("Something went wrong with tuple $(z) of type $(typeof(z))")
        end
        cycle += 1
    end
end

"""
    sat(
        α::T1,
        z::Formula,
        a::A;
        rng = Random.GLOBAL_RNG,
        verbose::Bool=false,
        timeout::Union{Nothing,Int}=nothing,
        kwargs...
    )

Given a formula, return true if it is α-valid, i.e., there is not an interpretation that
does not satisfy the formula, nothing in case of timeout or out-of-memory error, false
otherwise.
"""
function sat(
    sz::SignedFormula{T1},
    h::A,
    choosenode::Function,
    metrics::Function...;
    verbose::Bool=false,
    timeout::Union{Nothing,Int}=nothing,
    kwargs...
) where {
    T<:Truth,
    D<:AbstractVector{T},
    A<:FiniteAlgebra{T,D},
    T1<:Truth
}
    if !isa(sz, SignedFormula{T}) sz = convert(SignedFormula{T}, sz)::SignedFormula{T} end
    metricheaps = Vector{MetricHeap}()   # Heaps to be used for tableau selection
    for metric ∈ metrics
        push!(metricheaps, MetricHeap(metric))
    end
    root = ManyValuedTableau(sz)
    for metricheap ∈ metricheaps
        push!(heap(metricheap), MetricHeapNode(metric(metricheap), root))
    end
    sat(metricheaps, choosenode, h; verbose, timeout, kwargs...)
end

function sat(
    z::Formula,
    h::A,
    choosenode::Function,
    metrics::Function...;
    verbose::Bool=false,
    timeout::Union{Nothing,Int}=nothing,
    kwargs...
) where {
    T<:Truth,
    D<:AbstractVector{T},
    A<:FiniteAlgebra{T,D}
}
    return sat(SignedFormula(true, (⊤, z)), h, choosenode, metrics...; verbose, timeout, kwargs...)
end

"""
    sat(
        z::Formula,
        h::A;
        rng = Random.GLOBAL_RNG,
        verbose::Bool=false,
        timeout::Union{Nothing,Int}=nothing,
        kwargs...
    ) where {
        T<:Truth,
        D<:AbstractVector{T},
        A<:FiniteAlgebra{T,D}
    }

Given a formula, return true if an interpretation that satisfies the formula exists, false
otherwise.
"""
function sat(
    z::Formula,
    h::A;
    rng = Random.GLOBAL_RNG,
    verbose::Bool=false,
    timeout::Union{Nothing,Int}=nothing,
    kwargs...
) where {
    T<:Truth,
    D<:AbstractVector{T},
    A<:FiniteAlgebra{T,D}
}
    randombranch(_::ManyValuedTableau{T}) where {T<:Truth} = rand(rng, Int)
    return sat(SignedFormula(true, (⊤, z)), h, roundrobin, randombranch; verbose, timeout, kwargs...)
end

"""
    prove(
        z::Formula,
        h::A;
        rng = Random.GLOBAL_RNG,
        verbose::Bool=false,
        timeout::Union{Nothing,Int}=nothing,
        kwargs...
    ) where {
        T<:Truth,
        D<:AbstractVector{T},
        A<:FiniteAlgebra{T,D}
    }

Given a formula, return true if it is valid, i.e., there is not an interpretation that does
not satisfy the formula, false otherwise.
"""
function prove(
    z::Formula,
    h::A;
    rng = Random.GLOBAL_RNG,
    verbose::Bool=false,
    timeout::Union{Nothing,Int}=nothing,
    kwargs...
) where {
    T<:Truth,
    D<:AbstractVector{T},
    A<:FiniteAlgebra{T,D}
}
    randombranch(_::ManyValuedTableau) = rand(rng, Int)
    r = sat(SignedFormula(false, (⊤, z)), h, roundrobin, randombranch; verbose, timeout, kwargs...)
    if isnothing(r)
        return r
    else
        return !r
    end
end

"""
    alphasat(
        α::T1,
        z::Formula,
        a::A;
        rng = Random.GLOBAL_RNG,
        verbose::Bool=false,
        timeout::Union{Nothing,Int}=nothing,
        kwargs...
    ) where {
        T<:Truth,
        D<:AbstractVector{T},
        A<:FiniteAlgebra{T,D},
        T1<:Truth
    }

Given a formula, return true if it is α-satisfiable, i.e., there is an interpretation such
that the formula assumes value of at least α, nothing in case of timeout or out-of-memory
error, false otherwise.
"""
function alphasat(
    α::T1,
    z::Formula,
    a::A;
    rng = Random.GLOBAL_RNG,
    verbose::Bool=false,
    timeout::Union{Nothing,Int}=nothing,
    kwargs...
) where {
    T<:Truth,
    D<:AbstractVector{T},
    A<:FiniteAlgebra{T,D},
    T1<:Truth
}
    if verbose
        println("Solving alphasat for: " * syntaxstring(α) * " ⪯ " * syntaxstring(z))
        println("Height: " * string(height(z)))
        println("Tokens: " * string(ntokens(z)))
        println()
    end
    randombranch(_::ManyValuedTableau) = rand(rng, Int)
    return sat(SignedFormula(true, (α, z)), a, roundrobin, randombranch; verbose, timeout, kwargs...)
end

"""
    alphaprove(
        α::T1,
        z::Formula,
        a::A;
        rng = Random.GLOBAL_RNG,
        verbose::Bool=false,
        timeout::Union{Nothing,Int}=nothing,
        kwargs...
    )

Given a formula, return true if it is α-valid, i.e., there is not an interpretation that
does not satisfy the formula, nothing in case of timeout or out-of-memory error, false
otherwise.
"""
function sat(
    sz::SignedFormula{T},
    h::A,
    choosenode::Function,
    metrics::Function...;
    verbose::Bool=false,
    timeout::Union{Nothing,Int}=nothing,
    kwargs...
) where {
    T<:Truth,
    N,
    A<:FiniteIndexAlgebra{N}
}
    if !isa(sz, SignedFormula{FiniteIndexTruth}) sz = convert(SignedFormula{FiniteIndexTruth}, sz)::SignedFormula{FiniteIndexTruth} end
    metricheaps = Vector{MetricHeap}()   # Heaps to be used for tableau selection
    for metric ∈ metrics
        push!(metricheaps, MetricHeap(metric))
    end
    root = ManyValuedTableau(sz)
    for metricheap ∈ metricheaps
        push!(heap(metricheap), MetricHeapNode(metric(metricheap), root))
    end
    sat(metricheaps, choosenode, h; verbose, timeout, kwargs...)
end

function sat(
    z::Formula,
    h::A,
    choosenode::Function,
    metrics::Function...;
    verbose::Bool=false,
    timeout::Union{Nothing,Int}=nothing,
    kwargs...
) where {
    N,
    A<:FiniteIndexAlgebra{N}
}
    return sat(SignedFormula(true, (⊤, z)), h, choosenode, metrics...; verbose, timeout, kwargs...)
end

"""
    sat(
        z::Formula,
        h::A;
        rng = Random.GLOBAL_RNG,
        verbose::Bool=false,
        timeout::Union{Nothing,Int}=nothing,
        kwargs...
    ) where {
        A<:FiniteAlgebra{T,D}
    }

Given a formula, return true if an interpretation that satisfies the formula exists, false
otherwise.
"""
function sat(
    z::Formula,
    h::A;
    rng = Random.GLOBAL_RNG,
    verbose::Bool=false,
    timeout::Union{Nothing,Int}=nothing,
    kwargs...
) where {
    N,
    A<:FiniteIndexAlgebra{N}
}
    randombranch(_::ManyValuedTableau{T}) where {T<:Truth} = rand(rng, Int)
    return sat(SignedFormula(true, (⊤, z)), h, roundrobin, randombranch; verbose, timeout, kwargs...)
end

"""
    prove(
        z::Formula,
        h::A;
        rng = Random.GLOBAL_RNG,
        verbose::Bool=false,
        timeout::Union{Nothing,Int}=nothing,
        kwargs...
    ) where {
        N,
        A<:FiniteIndexAlgebra{N}
    }

Given a formula, return true if it is valid, i.e., there is not an interpretation that does
not satisfy the formula, false otherwise.
"""
function prove(
    z::Formula,
    h::A;
    rng = Random.GLOBAL_RNG,
    verbose::Bool=false,
    timeout::Union{Nothing,Int}=nothing,
    kwargs...
) where {
    N,
    A<:FiniteIndexAlgebra{N}
}
    randombranch(_::ManyValuedTableau) = rand(rng, Int)
    r = sat(SignedFormula(false, (⊤, z)), h, roundrobin, randombranch; verbose, timeout, kwargs...)
    if isnothing(r)
        return r
    else
        return !r
    end
end

"""
    alphasat(
        α::T,
        z::Formula,
        a::A;
        rng = Random.GLOBAL_RNG,
        verbose::Bool=false,
        timeout::Union{Nothing,Int}=nothing,
        kwargs...
    ) where {
        T<:Truth,
        N,
        A<:FiniteIndexAlgebra{N}
    }

Given a formula, return true if it is α-satisfiable, i.e., there is an interpretation such
that the formula assumes value of at least α, nothing in case of timeout or out-of-memory
error, false otherwise.
"""
function alphasat(
    α::T,
    z::Formula,
    a::A;
    rng = Random.GLOBAL_RNG,
    verbose::Bool=false,
    timeout::Union{Nothing,Int}=nothing,
    kwargs...
) where {
    T<:Truth,
    N,
    A<:FiniteIndexAlgebra{N}
}
    if verbose
        println("Solving alphasat for: " * syntaxstring(α) * " ⪯ " * syntaxstring(z))
        println("Height: " * string(height(z)))
        println("Tokens: " * string(ntokens(z)))
        println()
    end
    randombranch(_::ManyValuedTableau) = rand(rng, Int)
    return sat(SignedFormula(true, (α, z)), a, roundrobin, randombranch; verbose, timeout, kwargs...)
end

"""
    alphaprove(
        α::T,
        z::Formula,
        a::A;
        rng = Random.GLOBAL_RNG,
        verbose::Bool=false,
        timeout::Union{Nothing,Int}=nothing,
        kwargs...
    ) where {
        T<:Truth,
        N,
        A<:FiniteIndexAlgebra{N}
    }

Given a formula, return true if it is α-valid, i.e., there is not an interpretation such
that the formula does not assume value of at least α, nothing in case of timeout or
out-of-memory error, false otherwise.
"""
function alphaprove(
    α::T,
    z::Formula,
    a::A;
    rng = Random.GLOBAL_RNG,
    verbose::Bool=false,
    timeout::Union{Nothing,Int}=nothing,
    kwargs...
) where {
    T<:Truth,
    N,
    A<:FiniteIndexAlgebra{N}
}
    if verbose
        println("Solving alphaprove for: " * syntaxstring(α) * " ⪯ " * syntaxstring(z, remove_redundant_parentheses=false))
        println("Height: " * string(height(z)))
        println("Tokens: " * string(ntokens(z)))
        println()
    end
    randombranch(_::ManyValuedTableau) = rand(rng, Int)
    r = sat(SignedFormula(false, (α, z)), a, roundrobin, randombranch; verbose, timeout, kwargs...)
    if isnothing(r)
        return r
    else
        return !r
    end
end