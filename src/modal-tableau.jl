function sat2(
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
                for l ∈ findleaves(en)
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
                for l ∈ findleaves(en)
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
                for l ∈ findleaves(en)
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
                for l ∈ findleaves(en)
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
                    !newnodes && l == node && push!(metricheaps, node)
                end
            # Base case
            else
                # # No condition matched, pushing node back into metricheaps
                # push!(metricheaps, node)
                println("ERROR: unrecognized operator")
                return nothing
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
                for l ∈ findleaves(en)
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
                for l ∈ findleaves(en)
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
                    !newnodes && l == node && push!(metricheaps, node)
                end
            # Base case
            else
                # No condition matched, pushing node back into metricheaps
                push!(metricheaps, node)
                # println("ERROR: unrecognized operator")
                # return nothing
            end
        else
            error("Something went wrong with tuple $(z) of type $(typeof(z))")
        end
        cycle += 1
    end
end

"""
    sat2(
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
function sat2(
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
    sat2(metricheaps, choosenode, h; verbose, timeout, kwargs...)
end

function sat2(
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
    return sat2(SignedFormula(true, (⊤, z)), h, choosenode, metrics...; verbose, timeout, kwargs...)
end

"""
    sat2(
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
function sat2(
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
    return sat2(SignedFormula(true, (⊤, z)), h, roundrobin, randombranch; verbose, timeout, kwargs...)
end
"""
    prove2(
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
function prove2(
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
    r = sat2(SignedFormula(false, (⊤, z)), h, roundrobin, randombranch; verbose, timeout, kwargs...)
    if isnothing(r)
        return r
    else
        return !r
    end
end

"""
    alphasat2(
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
function alphasat2(
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
        println("Solving alphasat2 for: " * syntaxstring(α) * " ⪯ " * syntaxstring(z))
        println("Height: " * string(height(z)))
        println("Tokens: " * string(ntokens(z)))
        println()
    end
    randombranch(_::ManyValuedTableau) = rand(rng, Int)
    return sat2(SignedFormula(true, (α, z)), a, roundrobin, randombranch; verbose, timeout, kwargs...)
end

"""
    alphaprove2(
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
function alphaprove2(
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
        println("Solving alphaprove2 for: " * syntaxstring(α) * " ⪯ " * syntaxstring(z, remove_redundant_parentheses=false))
        println("Height: " * string(height(z)))
        println("Tokens: " * string(ntokens(z)))
        println()
    end
    randombranch(_::ManyValuedTableau) = rand(rng, Int)
    r = sat2(SignedFormula(false, (α, z)), a, roundrobin, randombranch; verbose, timeout, kwargs...)
    if isnothing(r)
        return r
    else
        return !r
    end
end