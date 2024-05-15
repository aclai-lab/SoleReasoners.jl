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
        signedformula::SignedFormula{T},
        father::ManyValuedTableau{T}
    ) where {
        T<:Truth
    }
        ft = ManyValuedTableau(
            signedformula,
            father,
            Vector{ManyValuedTableau{T}}(),
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

isexpanded(ft::ManyValuedTableau) = ft.expanded
isclosed(ft::ManyValuedTableau) = ft.closed

expand!(ft::ManyValuedTableau) = ft.expanded = true

function close!(ft::ManyValuedTableau)
    ft.closed = true
    while !isempty(ft.children)
        c = pop!(ft.children)
        close!(c)
    end
end

isroot(ft::ManyValuedTableau) = isnothing(ft.father)

function findexpansionnode(ft::ManyValuedTableau{T}) where {T<:Truth}
    if isroot(ft) || isexpanded(ft.father)
        return ft
    else
        findexpansionnode(ft.father)
    end
end

isleaf(ft::ManyValuedTableau) = isempty(ft.children) ? true : false

function findleaves(leavesset::Vector{ManyValuedTableau}, ft::ManyValuedTableau)
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
    findleaves(Vector{ManyValuedTableau}(), ft)
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
                for l ∈ findleaves(en)
                    newnodes = false
                    for pair in pairs
                        newnode = false
                        # if !isbot(pair[1])
                            sy = SignedFormula(true, (pair[1], a))
                            # if !findformula(l, sy)
                                newnode = true
                                fta = ManyValuedTableau(sy, l)
                                push!(metricheaps, fta)
                            # end
                        # end
                        # if !isbot(pair[2])
                            sy = SignedFormula(true, (pair[2], b))
                            if newnode
                                newnodes = true
                                # if !findformula(fta, sy)
                                    ftb = ManyValuedTableau(sy, fta)
                                    push!(metricheaps, ftb)
                                # end
                            # elseif !findformula(l, sy)
                            else
                                newnodes = true
                                ftb = ManyValuedTableau(sy, l)
                                push!(metricheaps, ftb)
                            end
                        # end
                    end
                    if !newnodes && l == node
                        push!(metricheaps, node)
                    end
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
                for l ∈ findleaves(en)
                    newnodes = false
                    for pair in pairs
                        newnode = false
                        # if !istop(pair[1])
                            sy = SignedFormula(true, (a, pair[1]))
                            # if !findformula(l, sy)
                                newnode = true
                                fta = ManyValuedTableau(sy, l)
                                push!(metricheaps, fta)
                            # end
                        # end
                        # if !istop(pair[2])
                            sy = SignedFormula(true, (b, pair[2]))
                            if newnode
                                newnodes = true
                                # if !findformula(fta, sy)
                                    ftb = ManyValuedTableau(sy, fta)
                                    push!(metricheaps, ftb)
                                # end
                            # elseif !findformula(l, sy) # BUG
                            else
                                newnodes = true
                                ftb = ManyValuedTableau(sy, l)
                                push!(metricheaps, ftb)
                            end     
                        # end
                    end
                    if !newnodes && l == node
                        push!(metricheaps, node)
                    end
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
                for l ∈ findleaves(en)
                    newnodes = false
                    for pair in pairs
                        newnode = false                        
                        # if !isbot(pair[1])
                            sy = SignedFormula(true, (pair[1], a))
                            # if !findformula(l, sy)
                                newnode = true
                                fta = ManyValuedTableau(sy, l)
                                push!(metricheaps, fta)
                            # end
                        # end
                        # if !istop(pair[2])
                            sy = SignedFormula(true, (b, pair[2]))
                            if newnode
                                newnodes = true
                                # if !findformula(fta, sy)
                                    ftb = ManyValuedTableau(sy, fta)
                                    push!(metricheaps, ftb)
                            #     end
                            # elseif !findformula(l, sy) # BUG
                            else
                                newnodes = true
                                ftb = ManyValuedTableau(sy, l)
                                push!(metricheaps, ftb)
                            end
                        # end
                    end
                    if !newnodes && l == node
                        push!(metricheaps, node)
                    end
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
                for l ∈ findleaves(en)
                    newnodes = false
                    for pair in pairs
                        newnode = false
                        # if !istop(pair[1])
                            sy = SignedFormula(true, (a, pair[1]))
                            # if !findformula(l, sy)
                                newnode = true
                                fta = ManyValuedTableau(sy, l)
                                push!(metricheaps, fta)
                            # end
                        # end
                        # if !isbot(pair[2])
                            sy = SignedFormula(true, (pair[2], b))
                            if newnode
                                newnodes = true
                                # if !findformula(fta, sy)
                                    ftb = ManyValuedTableau(sy, fta)
                                    push!(metricheaps, ftb)
                            #     end
                            # elseif !findformula(l, sy) # BUG
                            else
                                newnodes = true
                                ftb = ManyValuedTableau(sy, l)
                                push!(metricheaps, ftb)
                            end 
                        # end    
                    end
                    if !newnodes && l == node
                        push!(metricheaps, node)
                    end
                end
            # Reversal Rules
            elseif !s && !isbot(z[1])
                # F(a→X) case
                for l ∈ findleaves(en)
                    newnodes = false
                    for ti ∈ maximalmembers(h, z[1])
                        sy = SignedFormula(true, (z[2], ti))
                        if !findformula(l, sy)
                            newnodes = true
                            fti = ManyValuedTableau(sy, l)
                            push!(metricheaps, fti)
                        end
                    end
                    if !newnodes && l == node
                        push!(metricheaps, node)
                    end
                end
            elseif s && !isbot(z[1])
                # T(a→X) case
                for l ∈ findleaves(en)
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
                    if !newnodes && l == node
                        push!(metricheaps, node)
                    end
                end
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
                for l ∈ findleaves(en)
                    newnodes = false
                    for pair in pairs
                        newnode = false
                        # if !istop(pair[1])
                            sy = SignedFormula(true, (a, pair[1]))
                            # if !findformula(l, sy)
                                newnode = true
                                fta = ManyValuedTableau(sy, l)
                                push!(metricheaps, fta)
                            # end
                        # end
                        # if !istop(pair[2])
                            sy = SignedFormula(true, (b, pair[2]))
                            if newnode
                                newnodes = true
                                # if !findformula(fta, sy)
                                    ftb = ManyValuedTableau(sy, fta)
                                    push!(metricheaps, ftb)
                            #     end
                            # elseif !findformula(l, sy) # BUG
                            else
                                newnodes = true
                                ftb = ManyValuedTableau(sy, l)
                                push!(metricheaps, ftb)
                            end     
                        # end
                    end
                    if !newnodes && l == node
                        push!(metricheaps, node)
                    end
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
                for l ∈ findleaves(en)
                    newnodes = false
                    for pair in pairs
                        newnode = false
                        # if !isbot(pair[1])
                            sy = SignedFormula(true, (pair[1], a))
                            # if !findformula(l, sy)
                                newnode = true
                                fta = ManyValuedTableau(sy, l)
                                push!(metricheaps, fta)
                            # end
                        # end
                        # if !isbot(pair[2])
                            sy = SignedFormula(true, (pair[2], b))
                            if newnode
                                newnodes = true
                                # if !findformula(fta, sy)
                                    ftb = ManyValuedTableau(sy, fta)
                                    push!(metricheaps, ftb)
                            #     end
                            # elseif !findformula(l, sy) # BUG
                            else
                                newnodes = true
                                ftb = ManyValuedTableau(sy, l)
                                push!(metricheaps, ftb)
                            end    
                        # end 
                    end
                    if !newnodes && l == node
                        push!(metricheaps, node)
                    end
                end
            # Reversal Rules
            elseif !s && !istop(z[2])
                # F(X→a) case
                for l ∈ findleaves(en)
                    newnodes = false
                    for ui ∈ minimalmembers(h, z[2])
                        sy = SignedFormula(true, (ui, z[1]))
                        if !findformula(l, sy)
                            newnodes = true
                            fui = ManyValuedTableau(sy, l)
                            push!(metricheaps, fui)
                        end
                    end
                    if !newnodes && l == node
                        push!(metricheaps, node)
                    end
                end
            elseif s && !istop(z[2])
                # T(X→A) case
                for l ∈ findleaves(en)
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
                    if !newnodes && l == node
                        push!(metricheaps, node)
                    end
                end
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
    oldrule::Bool = false,
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
                for l ∈ findleaves(en)
                    fta = ManyValuedTableau(SignedFormula(true, (z[1], a)), l)
                    push!(metricheaps, fta)
                    ftb = ManyValuedTableau(SignedFormula(true, (z[1], b)), fta)
                    push!(metricheaps, ftb)
                end
            elseif !s && token(z[2]) isa NamedConnective{:∧} && !isbot(z[1])
                # F(t→(A∧B)) case
                (a, b) = children(z[2])
                for l ∈ findleaves(en)
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
                push!(lvs, z[1])
                for l ∈ findleaves(en)
                    for ti ∈ lvs
                        if !isbot(ti)
                            fta = ManyValuedTableau(SignedFormula(true, (ti, a)), l)
                            push!(metricheaps, fta)
                            ftb = ManyValuedTableau(SignedFormula(false, (ti, b)), fta)
                            push!(metricheaps, ftb)
                        end
                    end           
                end
            elseif s && token(z[2]) isa NamedConnective{:→} && !isbot(z[1])
                if oldrule
                    # (OLD) T(t→(A→B)) case
                    (a, b) = children(z[2])
                    lvs = lesservalues(h, z[1])
                    push!(lvs, z[1])
                    for ti in lvs
                        if !isbot(ti)
                            for l ∈ findleaves(en)
                                fta = ManyValuedTableau(SignedFormula(false, (ti, a)), l)
                                push!(metricheaps, fta)
                                ftb = ManyValuedTableau(SignedFormula(true, (ti, b)), l)
                                push!(metricheaps, ftb)
                            end
                        end
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
                    for l ∈ findleaves(en)
                        for pair in pairs
                            fta = ManyValuedTableau(SignedFormula(true, (a, pair[1])), l)
                            push!(metricheaps, fta)
                            ftb = ManyValuedTableau(SignedFormula(true, (pair[2], b)), fta)
                            push!(metricheaps, ftb)
                        end
                    end
                end                
            elseif !s && !isbot(z[1])
                # F(a→X) case
                for l ∈ findleaves(en)
                    newnodes = false
                    for ti ∈ maximalmembers(h, z[1])
                        sy = SignedFormula(true, (z[2], ti))
                        if !findformula(l, sy)
                            newnodes = true
                            fti = ManyValuedTableau(sy, l)
                            push!(metricheaps, fti)
                        end
                    end
                    if !newnodes && l == node
                        push!(metricheaps, node)
                    end
                end
            elseif s && !isbot(z[1])
                # T(a→X) case
                for l ∈ findleaves(en)
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
                    if !newnodes && l == node
                        push!(metricheaps, node)
                    end
                end
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
                for l ∈ findleaves(en)
                    fta = ManyValuedTableau(SignedFormula(true, (a, z[2])), l)
                    push!(metricheaps, fta)
                    ftb = ManyValuedTableau(SignedFormula(true, (b, z[2])), fta)
                    push!(metricheaps, ftb)
                end
            elseif !s && token(z[1]) isa NamedConnective{:∨} && !istop(z[2])
                # F((A∨B)→t) case
                (a, b) = children(z[1])
                for l ∈ findleaves(en)
                    fta = ManyValuedTableau(SignedFormula(false, (a, z[2])), l)
                    push!(metricheaps, fta)
                    ftb = ManyValuedTableau(SignedFormula(false, (b, z[2])), l)
                    push!(metricheaps, ftb)
                end
            elseif !s && !istop(z[2])
                # F(X→a) case
                for l ∈ findleaves(en)
                    newnodes = false
                    for ui ∈ minimalmembers(h, z[2])
                        sy = SignedFormula(true, (ui, z[1]))
                        if !findformula(l, sy)
                            newnodes = true
                            fui = ManyValuedTableau(sy, l)
                            push!(metricheaps, fui)
                        end
                    end
                    if !newnodes && l == node
                        push!(metricheaps, node)
                    end
                end
            elseif s && !istop(z[2])
                # T(X→A) case
                for l ∈ findleaves(en)
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
                    if !newnodes && l == node
                        push!(metricheaps, node)
                    end
                end

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

function alphaprove(
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
