using Combinatorics: with_replacement_combinations, permutations
using SoleLogics.ManyValuedLogics: getdomain

"""
    mutable struct MVLTLFPTableau <: ManyValuedMultiModalTableau
        const judgement::Bool
        const assertion::NTuple{2,Formula}
        const world::Point1D
        const frame::ManyValuedLinearOrder
        const father::Union{MVLTLFPTableau,Nothing}
        const children::Vector{MVLTLFPTableau}
        expanded::Bool
        closed::Bool
    end

Tableau to reason about Many-Valued Linear Temporal Logic with Future and Past.
"""
mutable struct MVLTLFPTableau <: ManyValuedMultiModalTableau
    const judgement::Bool
    const assertion::NTuple{2,Formula}
    const world::Point1D
    const frame::ManyValuedLinearOrder
    const father::Union{MVLTLFPTableau,Nothing}
    const children::Vector{MVLTLFPTableau}
    expanded::Bool
    closed::Bool

    function MVLTLFPTableau(
        judgement::Bool,
        assertion::NTuple{2,Formula},
        world::Point1D,
        frame::ManyValuedLinearOrder
    )
        return new(
            judgement,
            assertion,
            world,
            frame,
            nothing,
            Vector{MVLTLFPTableau}(),
            false,
            false
        )
    end

    function MVLTLFPTableau(
        judgement::Bool,
        assertion::NTuple{2,Formula},
        world::Point1D,
        frame::ManyValuedLinearOrder,
        father::MVLTLFPTableau
    )
        newtableau = new(
            judgement,
            assertion,
            world,
            frame,
            father,
            Vector{MVLTLFPTableau}(),
            false,
            false
        )
        pushchild!(father, newtableau)
        return newtableau
    end
end

function worlds(::Type{MVLTLFPTableau}, frame::ManyValuedLinearOrder)
    return Point1D.([UInt8(1):UInt8(cardinality(frame))]...)
end

function newframes(t::MVLTLFPTableau, algebra::FiniteFLewAlgebra)
    f = frame(t)
    n = cardinality(f)
    combs = unique(
        [
            (
                collect.(
                    permutations.(
                        with_replacement_combinations(getdomain(algebra), n)
                    )
                )...
            )...
        ]
    )
    os = Vector{ManyValuedLinearOrder}([f])
    for ltzcomb in combs
        for gtzcomb in combs
            for eqzcomb in combs
                mvlt = Matrix(undef, n+1, n+1)
                mvlt[1:n, 1:n] = f.mvlt
                mvlt[1:n, n+1] = ltzcomb
                mvlt[n+1, 1:n] = gtzcomb
                mvlt[n+1, n+1] = FiniteTruth(2)
                mvlt = SMatrix(mvlt)
                mveq = Matrix(undef, n+1, n+1)
                mveq[1:n, 1:n] = f.mveq
                mveq[1:n, n+1] = eqzcomb
                mveq[n+1, 1:n] = eqzcomb
                mveq[n+1, n+1] = FiniteTruth(1)
                mveq = SMatrix(mveq)
                if isaManyValuedLinearOrder(mvlt, mveq, algebra)
                    push!(
                        os,
                        @inbounds ManyValuedLinearOrder(mvlt, mveq, algebra)
                    )
                end
            end
        end
    end
    return os
end

function alphasat(
    ::Type{MVLTLFPTableau},
    α::T,
    φ::Formula,
    algebra::FiniteFLewAlgebra,
    choosenode::Function,
    metrics::Function...;
    timeout::Union{Nothing, Int} = nothing
) where {
    T<:Truth
}
    if !isa(α, FiniteTruth) α = convert(FiniteTruth, α)::FiniteTruth end
    x = Point1D(1)
    o = ManyValuedLinearOrder(
        SMatrix{1,1}([FiniteTruth(2)]),
        SMatrix{1,1}([FiniteTruth(1)]),
        algebra
    )
    tableau = MVLTLFPTableau(true, (α, φ), x, o)
    metricheaps = Vector{MetricHeap}()  # Heaps to be used for node selection
    for metric ∈ metrics
        push!(metricheaps, MetricHeap(metric))
    end
    for metricheap ∈ metricheaps
        push!(heap(metricheap), MetricHeapNode(metric(metricheap), tableau))
    end
    return alphasat(metricheaps, choosenode, algebra; timeout)
end

function alphasat(
    ::Type{MVLTLFPTableau},
    α::T,
    φ::Formula,
    algebra::FiniteFLewAlgebra;
    timeout::Union{Nothing, Int} = nothing
) where {
    T<:Truth
}
    return alphasat(
        MVLTLFPTableau,
        α,
        φ,
        algebra,
        roundrobin!,
        randombranch;
        timeout
    )
end

function alphaval(
    ::Type{MVLTLFPTableau},
    α::T,
    φ::Formula,
    algebra::FiniteFLewAlgebra,
    choosenode::Function,
    metrics::Function...;
    timeout::Union{Nothing, Int} = nothing
) where {
    T<:Truth
}
    if !isa(α, FiniteTruth) α = convert(FiniteTruth, α)::FiniteTruth end
    x = Point1D(1)
    o = ManyValuedLinearOrder(
        SMatrix{1,1}([FiniteTruth(2)]),
        SMatrix{1,1}([FiniteTruth(1)]),
        algebra
    )
    tableau = MVLTLFPTableau(false, (α, φ), x, o)
    metricheaps = Vector{MetricHeap}()  # Heaps to be used for node selection
    for metric ∈ metrics
        push!(metricheaps, MetricHeap(metric))
    end
    for metricheap ∈ metricheaps
        push!(heap(metricheap), MetricHeapNode(metric(metricheap), tableau))
    end
    r = alphasat(metricheaps, choosenode, algebra; timeout)
    if isnothing(r)
        return r
    else
        return !r
    end
end

function alphaval(
    ::Type{MVLTLFPTableau},
    α::T,
    φ::Formula,
    algebra::FiniteFLewAlgebra;
    timeout::Union{Nothing, Int} = nothing
) where {
    T<:Truth
}
    return alphaval(
        MVLTLFPTableau,
        α,
        φ,
        algebra,
        roundrobin!,
        randombranch;
        timeout
    )
end
