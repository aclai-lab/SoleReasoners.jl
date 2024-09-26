mutable struct HybridTableau{T<:Truth} <: AbstractTableau
    const signedformula::SignedFormula{T}
    const father::Union{HybridTableau{T}, Nothing}
    children::Vector{HybridTableau{T}}
    expanded::Bool
    closed::Bool
    smtconstraints::Vector{String}

    function HybridTableau(
        signedformula::SignedFormula{T},
        father::HybridTableau{T},
        children::Vector{HybridTableau{T}},
        expanded::Bool,
        closed::Bool,
        smtconstraints::Vector{String}
    ) where {
        T<:Truth
    }
        return new{T}(signedformula, father, children, expanded, closed, smtconstraints)
    end

    function HybridTableau(
        signedformula::SignedFormula{T},
        _::Nothing,
        children::Vector{HybridTableau{T}},
        expanded::Bool,
        closed::Bool,
        smtconstraints::Vector{String}
    ) where {
        T<:Truth
    }
        return new{T}(signedformula, nothing, children, expanded, closed, smtconstraints)
    end

    function HybridTableau(
        signedformula::SignedFormula{T1},
        father::HybridTableau{T}
    ) where {
        T1<:Truth,
        T<:Truth
    }
        if !isa(signedformula, SignedFormula{T})
            signedformula = convert(SignedFormula{T}, signedformula)::SignedFormula{T}
        end
        ft = HybridTableau(
            signedformula,
            father,
            Vector{HybridTableau{T}}(),
            false,
            false,
            father.smtconstraints
        )
        pushchild!(father, ft)
        return ft
    end

    function HybridTableau(
        signedformula::SignedFormula{T1},
        father::HybridTableau{T},
        newsmtconstraints::Vector{String}
    ) where {
        T1<:Truth,
        T<:Truth
    }
        if !isa(signedformula, SignedFormula{T})
            signedformula = convert(SignedFormula{T}, signedformula)::SignedFormula{T}
        end
        ft = HybridTableau(
            signedformula,
            father,
            Vector{HybridTableau{T}}(),
            false,
            false,
            [father.smtconstraints; newsmtconstraints]
        )
        pushchild!(father, ft)
        return ft
    end

    function HybridTableau(signedformula::SignedFormula{T}) where {T<:Truth}
        return HybridTableau(
            signedformula,
            nothing,
            Vector{HybridTableau{T}}(),
            false,
            false,
            Vector{String}()
        )
    end
end

addconstraint!(ft::HybridTableau, c::String) = push!(ft.smtconstraints, c)

function findsimilar(
    ft::HybridTableau,
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

function findformula(ft::HybridTableau, sz::SignedFormula)
    sy = ft.signedformula
    sz == sy && return true
    while !isroot(ft)
        ft = ft.father
        sy = ft.signedformula
        sz == sy && return true
    end
    return false
end

function hybridsat(
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
        if isexpanded(node) # found a (possibly) satisfiable branch
            if isempty(node.smtconstraints)
                verbose && println(node) # print satisfiable branch
                return true
            else
                ## check smtconstraints
                smtfile = "(declare-sort A)\n"
                for i ∈ 1:length(getdomain(h))
                    smtfile *= "(declare-const a$i A)\n"
                end
                smtfile *= "(assert (distinct"
                for i ∈ 1:length(getdomain(h))
                    smtfile *= " a$i"
                end
                smtfile *= "))\n(declare-fun join (A A) A)\n(declare-fun meet (A A) A)\n(declare-fun monoid (A A) A)\n(declare-fun implication (A A) A)\n"
                for i ∈ 1:length(getdomain(h))
                    for j ∈ 1:length(getdomain(h))
                        smtfile *= "(assert (= (join a$i a$j) a$(findfirst(item -> item == h.join(getdomain(h)[i], getdomain(h)[j]), getdomain(h)))))\n"
                        smtfile *= "(assert (= (meet a$i a$j) a$(findfirst(item -> item == h.meet(getdomain(h)[i], getdomain(h)[j]), getdomain(h)))))\n"
                        smtfile *= "(assert (= (monoid a$i a$j) a$(findfirst(item -> item == h.monoid(getdomain(h)[i], getdomain(h)[j]), getdomain(h)))))\n"
                        smtfile *= "(assert (= (implication a$i a$j) a$(findfirst(item -> item == h.implication(getdomain(h)[i], getdomain(h)[j]), getdomain(h)))))\n"
                    end
                end
                smtfile *= "(define-fun precedeq ((x A) (y A)) Bool (= (meet x y) x))\n"
                for str ∈ node.smtconstraints
                    smtfile *= str * "\n"
                end
                smtfile *= "(check-sat)"
                b = IOBuffer()
                touch("temp.smt2")
                open("temp.smt2", "w") do file
                    write(file, smtfile)
                end
                run(pipeline(`z3 temp.smt2`, stdout = b))
                rm("temp.smt2")
                if take!(b) == UInt8[0x73, 0x61, 0x74, 0x0a]
                    verbose && println(node) # print satisfiable branch
                    return true
                else
                    return false
                end
            end
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
            if s 
                if convert(FiniteTruth, z[1]) ∉ getdomain(h)
                    if convert(FiniteTruth, z[2]) ∉ getdomain(h)
                        for l ∈ leaves(en)
                            addconstraint!(l, "(assert (precedeq $(z[1].label) $(z[2].label)))\n")
                        end
                    else
                        for l ∈ leaves(en)
                            addconstraint!(l, "(assert (precedeq $(z[1].label) a$(findfirst(item -> item == convert(FiniteTruth, z[2]), getdomain(h)))))\n")
                        end
                    end
                elseif convert(FiniteTruth, z[2]) ∉ getdomain(h)
                    for l ∈ leaves(en)
                        addconstraint!(l, "(assert (precedeq a$(findfirst(item -> item == convert(FiniteTruth, z[1]), getdomain(h))) $(z[2].label)))\n")
                    end
                elseif !precedeq(h, z[1], z[2])
                    # T(a→b) where a≰b case
                    close!(en)
                end
            end
            if !s && precedeq(h, z[1], z[2]) && !isbot(z[1]) && !istop(z[2])
                # F(a→b) where a≤b and a≠⊥ and b≠⊤ case
                close!(en)
            elseif !s && isbot(z[1])
                # F(⊥→X) case
                close!(en)
            elseif !s && istop(z[2])
                # F(X→⊤) case
                close!(en)
            elseif findsimilar(en, h)   # TODO: check
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
            elseif isa(z[2], Atom)
                push!(metricheaps, node)
            # Strong conjunction Rules
            elseif s && token(z[2]) isa NamedConnective{:∧} && !isbot(z[1])
                # T(t→(A∧B)) case
                (a, b) = children(z[2])
                x, y = FiniteTruth.(["x$(string(cycle))", "y$(string(cycle))"])
                xsmtc = "(assert (or"
                ysmtc = "(assert (or"
                for value in 1:length(getdomain(h))
                    xsmtc *= " (= x$(string(cycle)) a$(string(value)))"
                    ysmtc *= " (= y$(string(cycle)) a$(string(value)))"
                end
                xsmtc *= "))"
                ysmtc *= "))"
                newsmtc = [
                    "(declare-const x$(string(cycle)) A)",
                    "(declare-const y$(string(cycle)) A)",
                    xsmtc,
                    ysmtc,
                    "(assert (precedeq a$(findfirst(item -> item == z[1], getdomain(h))) (monoid x$(string(cycle)) y$(string(cycle)))))"
                ]
                for l in leaves(en)                    
                    fta = HybridTableau(SignedFormula(true, (x, a)), l)
                    push!(metricheaps, fta)
                    ftb = HybridTableau(SignedFormula(true, (y, b)), fta, newsmtc)
                    push!(metricheaps, ftb)
                end                
            elseif !s && token(z[2]) isa NamedConnective{:∧} && !isbot(z[1])
                # F(t→(A∧B)) case
                (a, b) = children(z[2])
                x, y = FiniteTruth.(["x$(string(cycle))", "y$(string(cycle))"])
                xsmtc = "(assert (or"
                ysmtc = "(assert (or"
                for value in 1:length(getdomain(h))
                    xsmtc *= " (= x$(string(cycle)) a$(string(value)))"
                    ysmtc *= " (= y$(string(cycle)) a$(string(value)))"
                end
                xsmtc *= "))"
                ysmtc *= "))"
                newsmtc = [
                    "(declare-const x$(string(cycle)) A)",
                    "(declare-const y$(string(cycle)) A)",
                    xsmtc,
                    ysmtc,
                    "(assert (not (precedeq a$(findfirst(item -> item == z[1], getdomain(h))) (monoid x$(string(cycle)) y$(string(cycle))))))"
                ]
                for l in leaves(en)                    
                    fta = HybridTableau(SignedFormula(true, (a, x)), l)
                    push!(metricheaps, fta)
                    ftb = HybridTableau(SignedFormula(true, (b, y)), fta, newsmtc)
                    push!(metricheaps, ftb)
                end        
            # Implication Rules
            elseif s && token(z[2]) isa NamedConnective{:→} && !isbot(z[1])
                # T(t→(A→B)) case
                (a, b) = children(z[2])
                x, y = FiniteTruth.(["x$(string(cycle))", "y$(string(cycle))"])
                xsmtc = "(assert (or"
                ysmtc = "(assert (or"
                for value in 1:length(getdomain(h))
                    xsmtc *= " (= x$(string(cycle)) a$(string(value)))"
                    ysmtc *= " (= y$(string(cycle)) a$(string(value)))"
                end
                xsmtc *= "))"
                ysmtc *= "))"
                newsmtc = [
                    "(declare-const x$(string(cycle)) A)",
                    "(declare-const y$(string(cycle)) A)",
                    xsmtc,
                    ysmtc,
                    "(assert (precedeq a$(findfirst(item -> item == z[1], getdomain(h))) (implication x$(string(cycle)) y$(string(cycle)))))"
                ]
                for l in leaves(en)                    
                    fta = HybridTableau(SignedFormula(true, (a, x)), l)
                    push!(metricheaps, fta)
                    ftb = HybridTableau(SignedFormula(true, (y, b)), fta, newsmtc)
                    push!(metricheaps, ftb)
                end       
            elseif !s && token(z[2]) isa NamedConnective{:→} && !isbot(z[1])
                # F(t→(A→B)) case
                (a, b) = children(z[2])
                x, y = FiniteTruth.(["x$(string(cycle))", "y$(string(cycle))"])
                xsmtc = "(assert (or"
                ysmtc = "(assert (or"
                for value in 1:length(getdomain(h))
                    xsmtc *= " (= x$(string(cycle)) a$(string(value)))"
                    ysmtc *= " (= y$(string(cycle)) a$(string(value)))"
                end
                xsmtc *= "))"
                ysmtc *= "))"
                newsmtc = [
                    "(declare-const x$(string(cycle)) A)",
                    "(declare-const y$(string(cycle)) A)",
                    xsmtc,
                    ysmtc,
                    "(assert (not (precedeq a$(findfirst(item -> item == z[1], getdomain(h))) (implication x$(string(cycle)) y$(string(cycle))))))"
                ]
                for l in leaves(en)                    
                    fta = HybridTableau(SignedFormula(true, (x, a)), l)
                    push!(metricheaps, fta)
                    ftb = HybridTableau(SignedFormula(true, (b, y)), fta, newsmtc)
                    push!(metricheaps, ftb)
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
                            fti = HybridTableau(sy, l)
                            push!(metricheaps, fti)
                        else  # Here there should be a branch and I need to keep track of it
                            sy = SignedFormula(true, (⊤, ⊤))    # Fake node (always true)
                            fti = HybridTableau(sy, l)
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
                            fti = HybridTableau(sy, fti)
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
            elseif isa(z[1], Atom)
                push!(metricheaps, node)
            # Strong disjunction rules
            elseif s && token(z[1]) isa NamedConnective{:∨} && !istop(z[2])
                # T((A∨B)→t) case
                (a, b) = children(z[1])
                x, y = FiniteTruth.(["x$(string(cycle))", "y$(string(cycle))"])
                xsmtc = "(assert (or"
                ysmtc = "(assert (or"
                for value in 1:length(getdomain(h))
                    xsmtc *= " (= x$(string(cycle)) a$(string(value)))"
                    ysmtc *= " (= y$(string(cycle)) a$(string(value)))"
                end
                xsmtc *= "))"
                ysmtc *= "))"
                newsmtc = [
                    "(declare-const x$(string(cycle)) A)",
                    "(declare-const y$(string(cycle)) A)",
                    xsmtc,
                    ysmtc,
                    "(assert (precedeq (join x$(string(cycle)) y$(string(cycle))) a$(findfirst(item -> item == z[2], getdomain(h)))))"
                ]
                for l in leaves(en)                    
                    fta = HybridTableau(SignedFormula(true, (a, x)), l)
                    push!(metricheaps, fta)
                    ftb = HybridTableau(SignedFormula(true, (b, y)), fta, newsmtc)
                    push!(metricheaps, ftb)
                end       
            elseif !s && token(z[1]) isa NamedConnective{:∨} && !istop(z[2])
                # F((A∨B)→t) case
                (a, b) = children(z[1])
                x, y = FiniteTruth.(["x$(string(cycle))", "y$(string(cycle))"])
                xsmtc = "(assert (or"
                ysmtc = "(assert (or"
                for value in 1:length(getdomain(h))
                    xsmtc *= " (= x$(string(cycle)) a$(string(value)))"
                    ysmtc *= " (= y$(string(cycle)) a$(string(value)))"
                end
                xsmtc *= "))"
                ysmtc *= "))"
                newsmtc = [
                    "(declare-const x$(string(cycle)) A)",
                    "(declare-const y$(string(cycle)) A)",
                    xsmtc,
                    ysmtc,
                    "(assert (not (precedeq (join x$(string(cycle)) y$(string(cycle))) a$(findfirst(item -> item == z[2], getdomain(h))))))"
                ]
                for l in leaves(en)                    
                    fta = HybridTableau(SignedFormula(true, (x, a)), l)
                    push!(metricheaps, fta)
                    ftb = HybridTableau(SignedFormula(true, (y, b)), fta, newsmtc)
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
                            fui = HybridTableau(sy, l)
                            push!(metricheaps, fui)
                        else  # Here there should be a branch and I need to keep track of it
                            sy = SignedFormula(true, (⊤, ⊤))    # Fake node (always true)
                            fti = HybridTableau(sy, l)
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
                            fui = HybridTableau(sy, fui)
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
    hybridsat(
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
function hybridsat(
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
    root = HybridTableau(sz)
    for metricheap ∈ metricheaps
        push!(heap(metricheap), MetricHeapNode(metric(metricheap), root))
    end
    hybridsat(metricheaps, choosenode, h; verbose, timeout, kwargs...)
end

function hybridsat(
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
    return hybridsat(SignedFormula(true, (⊤, z)), h, choosenode, metrics...; verbose, timeout, kwargs...)
end

"""
    hybridsat(
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
function hybridsat(
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
    randombranch(_::HybridTableau{T}) where {T<:Truth} = rand(rng, Int)
    return hybridsat(SignedFormula(true, (⊤, z)), h, roundrobin, randombranch; verbose, timeout, kwargs...)
end

"""
    hybridprove(
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
function hybridprove(
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
    randombranch(_::HybridTableau) = rand(rng, Int)
    r = hybridsat(SignedFormula(false, (⊤, z)), h, roundrobin, randombranch; verbose, timeout, kwargs...)
    if isnothing(r)
        return r
    else
        return !r
    end
end

"""
    hybridalphasat(
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
function hybridalphasat(
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
        println("Solving hybridalphasat for: " * syntaxstring(α) * " ⪯ " * syntaxstring(z))
        println("Height: " * string(height(z)))
        println("Tokens: " * string(ntokens(z)))
        println()
    end
    randombranch(_::HybridTableau) = rand(rng, Int)
    return hybridsat(SignedFormula(true, (α, z)), a, roundrobin, randombranch; verbose, timeout, kwargs...)
end

"""
    hybridalphaprove(
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

Given a formula, return true if it is α-valid, i.e., there is not an interpretation such
that the formula does not assume value of at least α, nothing in case of timeout or
out-of-memory error, false otherwise.
"""
function hybridalphaprove(
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
        println("Solving hybridalphaprove for: " * syntaxstring(α) * " ⪯ " * syntaxstring(z, remove_redundant_parentheses=false))
        println("Height: " * string(height(z)))
        println("Tokens: " * string(ntokens(z)))
        println()
    end
    randombranch(_::HybridTableau) = rand(rng, Int)
    r = hybridsat(SignedFormula(false, (α, z)), a, roundrobin, randombranch; verbose, timeout, kwargs...)
    if isnothing(r)
        return r
    else
        return !r
    end
end
