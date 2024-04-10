"""
All formulas appearing in the tableau will be bounding implications, i.e.,
a → A (or A → a), where a is a propositional constant and asserting a ≤ A (resp. A ≤ a)
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
        "( $(syntaxstring(sz.boundingimplication[1])) )"*
        " ⪯ "*
        "( $(syntaxstring(sz.boundingimplication[2])) )"*
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

mutable struct ManyValuedTableau{T<:Truth} <: AbstractTableau
    const signedformula::SignedFormula{T}
    const father::Union{ManyValuedTableau{T}, Nothing}
    children::Set{ManyValuedTableau{T}}
    expanded::Bool
    closed::Bool

    function ManyValuedTableau(
        signedformula::SignedFormula{T},
        father::ManyValuedTableau{T},
        children::Set{ManyValuedTableau{T}},
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
        children::Set{ManyValuedTableau{T}},
        expanded::Bool,
        closed::Bool
    ) where {
        T<:Truth
    }
        return new{T}(signedformula, nothing, children, expanded, closed)
    end

    function ManyValuedTableau(
        signedformula::SignedFormula{T},
        father::ManyValuedTableau{T}
    ) where {
        T<:Truth
    }
        ft = ManyValuedTableau(
            signedformula,
            father,
            Set{ManyValuedTableau{T}}(),
            false,
            false
        )
        pushchildren!(father, ft)
        return ft
    end

    function ManyValuedTableau(signedformula::SignedFormula{T}) where {T<:Truth}
        return ManyValuedTableau(
            signedformula,
            nothing,
            Set{ManyValuedTableau{T}}(),
            false,
            false
        )
    end
end

isexpanded(ft::ManyValuedTableau) = ft.expanded
isclosed(ft::ManyValuedTableau) = ft.expanded

expand!(ft::ManyValuedTableau) = ft.expanded = true
close!(ft::ManyValuedTableau) = ft.closed = true

isroot(ft::ManyValuedTableau) = isnothing(ft.father)

function findexpansionnode(ft::ManyValuedTableau{T}) where {T<:Truth}
    if isexpanded(ft)
        return nothing
    elseif isroot(ft) || isexpanded(ft.father)
        return ft
    else
        findexpansionnode(ft.father)
    end
end

isleaf(ft::ManyValuedTableau) = isempty(ft.children) ? true : false

function findleaves(leavesset::Set{ManyValuedTableau}, ft::ManyValuedTableau)
    children = ft.children
    if isempty(children)
        push!(leavesset, ft)
    else
        for child ∈ children
            findleaves(leavesset, child)
        end
    end
    return leavesset
end

function findleaves(ft::ManyValuedTableau)
    findleaves(Set{ManyValuedTableau}(), ft)
end

function pushchildren!(ft::ManyValuedTableau, children::ManyValuedTableau...)
    push!(ft.children, children...)
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
    T<:Truth,
    D<:AbstractVector{T},
    A<:FiniteAlgebra{T,D}
}
    sz = ft.signedformula
    s = sz.sign
    z = sz.boundingimplication
    if s
        # Looking for F(a→X) where a≤b
        while !isroot(ft)
            ft = ft.father
            sy = ft.signedformula
            y = sy.boundingimplication
            if y[1] isa Truth && !sy.sign && z[2] == y[2] && precedeq(h, y[1], z[1])
                return true
            end
        end
    else
        # Looking for T(b→X) where a≤b
        while !isroot(ft)
            ft = ft.father
            sy = ft.signedformula
            y = sy.boundingimplication
            if y[1] isa Truth && sy.sign && z[2] == y[2] && precedeq(h, z[1], y[1])
                return true
            end
        end
    end
    return false
end

function sat(
    leaves::Vector{MetricHeap},
    chooseleaf::Function,
    h::FiniteFLewAlgebra{T,D}
) where {
    T<:Truth,
    D<:AbstractVector{T}
}
    cycle = 0
    while true

        # if using too much memory, kill execution to avoid crashes
        if cycle%10==0 && getfreemem() < gettotmem()*5e-2
            error("Too much memory being used, exiting")
        end

        leaf = chooseleaf(leaves, cycle)
        isnothing(leaf) && return false # all branches are closed
        en = findexpansionnode(leaf)
        isnothing(en) && return true    # found a satisfiable branch
        isclosed(en) && continue
        sz = en.signedformula
        if !isa(sz, SignedFormula{T})
            sz = convert(SignedFormula{T}, sz)::SignedFormula{T}
        end
        s = sz.sign
        z = sz.boundingimplication

        if z isa Tuple{Truth, Truth}
            # Branch Closure Conditions
            if s && !precedeq(h, z[1], z[2])
                # T(a→b) where a≰b case
                close!(en)
            elseif !s && precedeq(h, z[1], z[2]) && !isbot(z[1]) && !isbot(z[2])
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
                # No condition matched, pushing leaf back into leaves
                expand!(en)
                push!(leaves, leaf)
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
                expand!(en)
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
                for l ∈ findleaves(en)
                    for pair in pairs
                        fta = ManyValuedTableau(SignedFormula(true, (pair[1], a)), l)
                        ftb = ManyValuedTableau(SignedFormula(true, (pair[2], b)), fta)
                        push!(leaves, ftb)
                    end
                end
            elseif !s && token(z[2]) isa NamedConnective{:∧} && !isbot(z[1])
                # F(t→(A∧B)) case
                expand!(en)
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
                for l ∈ findleaves(en)
                    for pair in pairs
                        fta = ManyValuedTableau(SignedFormula(true, (a, pair[1])), l)
                        ftb = ManyValuedTableau(SignedFormula(true, (b, pair[2])), fta)
                        push!(leaves, ftb)
                    end
                end
            # Implication Rules
            elseif !s && token(z[2]) isa NamedConnective{:→} && !isbot(z[1])
                # F(t→(A→B)) case
                expand!(en)
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
                for l ∈ findleaves(en)
                    for pair in pairs
                        fta = ManyValuedTableau(SignedFormula(true, (pair[1], a)), l)
                        ftb = ManyValuedTableau(SignedFormula(true, (b, pair[2])), fta)
                        push!(leaves, ftb)
                    end
                end
            elseif s && token(z[2]) isa NamedConnective{:→} && !isbot(z[1])
                # T(t→(A→B)) case
                expand!(en)
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
                for l ∈ findleaves(en)
                    for pair in pairs
                        fta = ManyValuedTableau(SignedFormula(true, (a, pair[1])), l)
                        ftb = ManyValuedTableau(SignedFormula(true, (pair[2], b)), fta)
                        push!(leaves, ftb)
                    end
                end
            # Atom case
            elseif z[2] isa Atom
                # a→X where X isa Atom case
                expand!(en)
                push!(leaves, leaf)
            # Reversal Rules
            elseif !s && !isbot(z[1])
                # F(a→X) case
                expand!(en)
                for l ∈ findleaves(en)
                    for ti ∈ maximalmembers(h, z[1])
                        fti = ManyValuedTableau(SignedFormula(true, (z[2], ti)), l)
                        push!(leaves, fti)
                    end
                end
            elseif s && !isbot(z[1])
                # T(a→X) case
                expand!(en)
                for l ∈ findleaves(en)
                    fti = l
                    for ti in maximalmembers(h, z[1])
                        fti = ManyValuedTableau(SignedFormula(false, (z[2], ti)), fti)
                    end
                    push!(leaves, fti)
                end
            # Base case
            else
                # No condition matched, pushing leaf back into leaves
                expand!(en)
                push!(leaves, leaf)
            end
        elseif z isa Tuple{Formula, T}
            # Branch Closure Conditions
            if !s && istop(z[2])
                # F(X→⊤) case
                close!(en)
            # Strong disjunction rules
            elseif s && token(z[1]) isa NamedConnective{:∨} && !istop(z[2])
                # T((A∨B)→t) case
                expand!(en)
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
                for l ∈ findleaves(en)
                    for pair in pairs
                        fta = ManyValuedTableau(SignedFormula(true, (a, pair[1])), l)
                        ftb = ManyValuedTableau(SignedFormula(true, (b, pair[2])), fta)
                        push!(leaves, ftb)
                    end
                end
            elseif !s && token(z[1]) isa NamedConnective{:∨} && !istop(z[2])
                # F((A∨B)→t) case
                expand!(en)
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
                for l ∈ findleaves(en)
                    for pair in pairs
                        fta = ManyValuedTableau(SignedFormula(true, (pair[1], a)), l)
                        ftb = ManyValuedTableau(SignedFormula(true, (pair[2], b)), fta)
                        push!(leaves, ftb)
                    end
                end
            # Reversal Rules
            elseif !s && !istop(z[2])
                # F(X→a) case
                expand!(en)
                for l ∈ findleaves(en)
                    for ui ∈ minimalmembers(h, z[2])
                        fti = ManyValuedTableau(SignedFormula(true, (ui, z[1])), l)
                        push!(leaves, fti)
                    end
                end
            elseif s && !istop(z[2])
                # T(a→X) case
                expand!(en)
                for l ∈ findleaves(en)
                    fui = l
                    for ui in minimalmembers(h, z[2])
                        fui = ManyValuedTableau(SignedFormula(false, (ui, z[1])), fui)
                    end
                    push!(leaves, fui)
                end
            # Base case
            else
                # No condition matched, pushing leaf back into leaves
                expand!(en)
                push!(leaves, leaf)
            end
        else
            error("Something went wrong with tuple $(z) of type $(typeof(z))")
        end
        cycle += 1
    end
end


function sat(
    leaves::Vector{MetricHeap},
    chooseleaf::Function,
    h::FiniteHeytingAlgebra{T,D};
    oldrule::Bool = false
) where {
    T<:Truth,
    D<:AbstractVector{T}
}
    cycle = 0
    while true

        # if using too much memory, kill execution to avoid crashes
        if cycle%10==0 && getfreemem() < gettotmem()*5e-2
            error("Too much memory being used, exiting")
        end

        leaf = chooseleaf(leaves, cycle)
        isnothing(leaf) && return false # all branches are closed
        en = findexpansionnode(leaf)
        isnothing(en) && return true    # found a satisfiable branch
        isclosed(en) && continue
        sz = en.signedformula
        if !isa(sz, SignedFormula{T})
            sz = convert(SignedFormula{T}, sz)::SignedFormula{T}
        end
        s = sz.sign
        z = sz.boundingimplication

        if z isa Tuple{Truth, Truth}
            # Branch Closure Conditions
            if s && !precedeq(h, z[1], z[2])
                # T(a→b) where a≰b case
                close!(en)
            elseif !s && precedeq(h, z[1], z[2]) && !isbot(z[1]) && !isbot(z[2])
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
                # No condition matched, pushing leaf back into leaves
                expand!(en)
                push!(leaves, leaf)
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
                expand!(en)
                (a, b) = children(z[2])
                for l ∈ findleaves(en)
                    fta = ManyValuedTableau(SignedFormula(true, (z[1], a)), l)
                    ftb = ManyValuedTableau(SignedFormula(true, (z[1], b)), fta)
                    push!(leaves, ftb)
                end
            elseif !s && token(z[2]) isa NamedConnective{:∧} && !isbot(z[1])
                # F(t→(A∧B)) case
                expand!(en)
                (a, b) = children(z[2])
                for l ∈ findleaves(en)
                    fta = ManyValuedTableau(SignedFormula(false, (z[1], a)), l)
                    push!(leaves, fta)
                    ftb = ManyValuedTableau(SignedFormula(false, (z[1], b)), l)
                    push!(leaves, ftb)
                end
            # Implication rules
            elseif !s && token(z[2]) isa NamedConnective{:→} && !isbot(z[1])
                # F(t→(A→B)) case
                expand!(en)
                (a, b) = children(z[2])
                lvs = lesservalues(h, z[1])
                push!(lvs, z[1])
                for l ∈ findleaves(en)
                    for ti ∈ lvs
                        isbot(ti) && continue
                        fta = ManyValuedTableau(SignedFormula(true, (ti, a)), l)
                        ftb = ManyValuedTableau(SignedFormula(false, (ti, b)), fta)
                        push!(leaves, ftb)
                    end                    
                end
            elseif oldrule && s && token(z[2]) isa NamedConnective{:→} && !isbot(z[1])
                # (OLD) T(t→(A→B)) case
                expand!(en)
                (a, b) = children(z[2])
                lvs = lesservalues(h, z[1])
                push!(lvs, z[1])
                for ti in lvs
                    if !isbot(ti)
                        for l ∈ findleaves(en)
                            ManyValuedTableau(SignedFormula(false, (ti, a)), l)
                            ManyValuedTableau(SignedFormula(true, (ti, b)), l)
                        end
                    end
                end
                for l ∈ findleaves(en)
                    push!(leaves, l)
                end
            elseif s && token(z[2]) isa NamedConnective{:→} && !isbot(z[1])
                # (NEW) T(t→(A→B)) case
                expand!(en)
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
                for l ∈ findleaves(en)
                    for pair in pairs
                        fta = ManyValuedTableau(SignedFormula(true, (a, pair[1])), l)
                        ftb = ManyValuedTableau(SignedFormula(true, (pair[2], b)), fta)
                        push!(leaves, ftb)
                    end
                end
            # Atom case
            elseif z[2] isa Atom
                # a→X where X isa Atom case
                expand!(en)
                push!(leaves, leaf)
            # Reversal Rules
            elseif !s && !isbot(z[1])
                # F(a→X) case
                expand!(en)
                for l ∈ findleaves(en)
                    for ti ∈ maximalmembers(h, z[1])
                        fti = ManyValuedTableau(SignedFormula(true, (z[2], ti)), l)
                        push!(leaves, fti)
                    end
                end
            elseif s && !isbot(z[1])
                # T(a→X) case
                expand!(en)
                for l ∈ findleaves(en)
                    fti = l
                    for ti in maximalmembers(h, z[1])
                        fti = ManyValuedTableau(SignedFormula(false, (z[2], ti)), fti)
                    end
                    push!(leaves, fti)
                end
            # Base case
            else
                # No condition matched, pushing leaf back into leaves
                expand!(en)
                push!(leaves, leaf)
            end
        elseif z isa Tuple{Formula, T}
            # Branch Closure Conditions
            if !s && istop(z[2])
                # F(X→⊤) case
                close!(en)
            # Weak disjunction Rules
            elseif s && token(z[1]) isa NamedConnective{:∨} && !istop(z[2])
                # T((A∨B)→t) case
                expand!(en)
                (a, b) = children(z[1])
                for l ∈ findleaves(en)
                    fta = ManyValuedTableau(SignedFormula(true, (a, z[2])), l)
                    ftb = ManyValuedTableau(SignedFormula(true, (b, z[2])), fta)
                    push!(leaves, ftb)
                end
            elseif !s && token(z[1]) isa NamedConnective{:∨} && !istop(z[2])
                # F((A∨B)→t) case
                expand!(en)
                (a, b) = children(z[1])
                for l ∈ findleaves(en)
                    fta = ManyValuedTableau(SignedFormula(false, (a, z[2])), l)
                    push!(leaves, fta)
                    ftb = ManyValuedTableau(SignedFormula(false, (b, z[2])), l)
                    push!(leaves, ftb)
                end
            # Reversal Rules
            elseif !s && !istop(z[2])
                # F(X→a) case
                expand!(en)
                for l ∈ findleaves(en)
                    for ui ∈ minimalmembers(h, z[2])
                        fti = ManyValuedTableau(SignedFormula(true, (ui, z[1])), l)
                        push!(leaves, fti)
                    end
                end
            elseif s && !istop(z[2])
                # T(a→X) case
                expand!(en)
                for l ∈ findleaves(en)
                    fui = l
                    for ui in minimalmembers(h, z[2])
                        fui = ManyValuedTableau(SignedFormula(false, (ui, z[1])), fui)
                    end
                    push!(leaves, fui)
                end
            # Base case
            else
                # No condition matched, pushing leaf back into leaves
                expand!(en)
                push!(leaves, leaf)
            end
        else
            error("Something went wrong with tuple $(z) of type $(typeof(z))")
        end
        cycle += 1
    end
end

function sat(
    sz::SignedFormula{T1},
    h::A,
    chooseleaf::Function,
    metrics::Function...;
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
    sat(metricheaps, chooseleaf, h; kwargs...)
end

function sat(
    z::Formula,
    h::A,
    chooseleaf::Function,
    metrics::Function...;
    kwargs...
) where {
    T<:Truth,
    D<:AbstractVector{T},
    A<:FiniteAlgebra{T,D}
}
    return sat(SignedFormula(true, (⊤, z)), h, chooseleaf, metrics...; kwargs...)
end

function sat(
    z::Formula,
    h::A;
    rng = Random.GLOBAL_RNG,
    kwargs...
) where {
    T<:Truth,
    D<:AbstractVector{T},
    A<:FiniteAlgebra{T,D}
}
    randombranch(_::ManyValuedTableau{T}) where {T<:Truth} = rand(rng, Int)
    return sat(SignedFormula(true, (⊤, z)), h, roundrobin, randombranch; kwargs...)
end

function prove(
    z::Formula,
    h::A;
    rng = Random.GLOBAL_RNG,
    kwargs...
) where {
    T<:Truth,
    D<:AbstractVector{T},
    A<:FiniteAlgebra{T,D}
}
    randombranch(_::ManyValuedTableau) = rand(rng, Int)
    return !sat(SignedFormula(false, (⊤, z)), h, roundrobin, randombranch; kwargs...)
end

function alphasat(
    α::T1,
    z::Formula,
    a::A;
    rng = Random.GLOBAL_RNG,
    kwargs...
) where {
    T<:Truth,
    D<:AbstractVector{T},
    A<:FiniteAlgebra{T,D},
    T1<:Truth
}
    randombranch(_::ManyValuedTableau) = rand(rng, Int)
    return sat(SignedFormula(true, (α, z)), a, roundrobin, randombranch; kwargs...)
end

function alphaprove(
    α::T1,
    z::Formula,
    a::A;
    rng = Random.GLOBAL_RNG,
    kwargs...
) where {
    T<:Truth,
    D<:AbstractVector{T},
    A<:FiniteAlgebra{T,D},
    T1<:Truth
}
    randombranch(_::ManyValuedTableau) = rand(rng, Int)
    return !sat(SignedFormula(false, (α, z)), a, roundrobin, randombranch; kwargs...)
end
