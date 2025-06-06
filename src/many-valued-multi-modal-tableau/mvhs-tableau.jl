using Base.Threads

"""
    mutable struct MVHSTableau <: ManyValuedMultiModalTableau
        const judgement::Bool
        const assertion::NTuple{2,Formula}
        const world::Interval
        const frame::ManyValuedLinearOrder
        const father::Union{MVHSTableau,Nothing}
        const children::Vector{MVHSTableau}
        expanded::Bool
        closed::Bool
    end

Tableau to reason about Many-Valued Halpern and Shoham's modal logic of time
intervals.
"""
mutable struct MVHSTableau <: ManyValuedMultiModalTableau
    const judgement::Bool
    const assertion::NTuple{2,Formula}
    const world::Interval
    const frame::ManyValuedLinearOrder
    const father::Union{MVHSTableau,Nothing}
    const children::Vector{MVHSTableau}
    expanded::Bool
    closed::Bool

    function MVHSTableau(
        judgement::Bool,
        assertion::NTuple{2,Formula},
        world::Interval,
        frame::ManyValuedLinearOrder
    )
        return new(
            judgement,
            assertion,
            world,
            frame,
            nothing,
            Vector{MVHSTableau}(),
            false,
            false
        )
    end

    function MVHSTableau(
        judgement::Bool,
        assertion::NTuple{2,Formula},
        world::Interval,
        frame::ManyValuedLinearOrder,
        father::MVHSTableau
    )
        newtableau = new(
            judgement,
            assertion,
            world,
            frame,
            father,
            Vector{MVHSTableau}(),
            false,
            false
        )
        pushchild!(father, newtableau)
        return newtableau
    end
end

function worlds(::Type{MVHSTableau}, frame::ManyValuedLinearOrder)
    points = Point1D.([UInt8(1):UInt8(cardinality(frame))]...)
    return map(
        x->(@inbounds Interval(x[1], x[2], frame)),
        Iterators.filter(
            x->isaInterval(x[1], x[2], frame),
            Iterators.product(points, points)
        )
    )
end

function newframes(
    t::MVHSTableau,
    algebra::FiniteFLewAlgebra;
    timeout=nothing,
    t0=nothing
)
    f = frame(t)
    n = cardinality(f)
    os = Vector{ManyValuedLinearOrder}([f])
    lock = Threads.ReentrantLock();
    zcombs = unique(
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
    @threads for ltzcomb in zcombs
        for gtzcomb in zcombs
            for eqzcomb in zcombs
                mvlt = Matrix(undef, n+1, n+1)
                mvlt[1:n, 1:n] = f.mvlt
                mvlt[1:n, n+1] = ltzcomb
                mvlt[n+1, 1:n] = gtzcomb
                mvlt[n+1, n+1] = FiniteTruth(2)
                mvlt = SMatrix{n+1,n+1,FiniteTruth}(mvlt)
                mveq = Matrix(undef, n+1, n+1)
                mveq[1:n, 1:n] = f.mveq
                mveq[1:n, n+1] = eqzcomb
                mveq[n+1, 1:n] = eqzcomb
                mveq[n+1, n+1] = FiniteTruth(1)
                mveq = SMatrix{n+1,n+1,FiniteTruth}(mveq)
                if isaManyValuedLinearOrder(mvlt, mveq, algebra)
                    oz = @inbounds ManyValuedLinearOrder(mvlt, mveq, algebra)
                    @lock lock push!(os, oz)
                    tcombs = unique(
                        [
                            (
                                collect.(
                                    permutations.(
                                        with_replacement_combinations(
                                            getdomain(algebra),
                                            n+1
                                        )
                                    )
                                )...
                            )...
                        ]
                    )
                    for lttcomb in tcombs
                        for gttcomb in tcombs
                            for eqtcomb in tcombs
                                if !isnothing(timeout) &&
                                   (time_ns()-t0)/1e9 > timeout
                                    return nothing
                                end
                                mvlt = Matrix(undef, n+2, n+2)
                                mvlt[1:n+1, 1:n+1] = oz.mvlt
                                mvlt[1:n+1, n+2  ] = lttcomb
                                mvlt[n+2,   1:n+1] = gttcomb
                                mvlt[n+2,   n+2  ] = FiniteTruth(2)
                                mvlt = SMatrix{n+2,n+2,FiniteTruth}(mvlt)
                                mveq = Matrix(undef, n+2, n+2)
                                mveq[1:n+1, 1:n+1] = oz.mveq
                                mveq[1:n+1, n+2  ] = eqtcomb
                                mveq[n+2,   1:n+1] = eqtcomb
                                mveq[n+2,   n+2  ] = FiniteTruth(1)
                                mveq = SMatrix{n+2,n+2,FiniteTruth}(mveq)
                                if isaManyValuedLinearOrder(mvlt, mveq, algebra)
                                    ot = @inbounds ManyValuedLinearOrder(
                                        mvlt,
                                        mveq,
                                        algebra
                                    )
                                    @lock lock push!(os, ot)
                                end
                            end
                        end
                    end
                end
            end
        end
    end
    return os
end

function alphasat(
    ::Type{MVHSTableau},
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
    x, y = Point1D.([1, 2])
    os = Vector{ManyValuedLinearOrder}()
    for δ in getdomain(algebra)
        istop(δ) && continue
        for β in getdomain(algebra)
            isbot(β) && continue
            for γ in getdomain(algebra)
                mvlt = SMatrix{2,2,FiniteTruth}(
                    [[FiniteTruth(2) β]; [γ FiniteTruth(2)]]
                )
                mveq = SMatrix{2,2,FiniteTruth}(
                    [[FiniteTruth(1) δ]; [δ FiniteTruth(1)]]
                )
                if isaManyValuedLinearOrder(mvlt, mveq, algebra)
                    push!(
                        os,
                        @inbounds ManyValuedLinearOrder(mvlt, mveq, algebra)
                    )
                end
            end
        end
    end
    metricheaps = Vector{MetricHeap}()  # Heaps to be used for node selection
    for metric ∈ metrics
        push!(metricheaps, MetricHeap(metric))
    end
    for o ∈ os
        !isaInterval(x, y, o) && continue
        i = @inbounds Interval(x, y, o)
        tableau = MVHSTableau(true, (α, φ), i, o)
        for metricheap ∈ metricheaps
            push!(heap(metricheap), MetricHeapNode(metric(metricheap), tableau))
        end
    end
    return alphasat(metricheaps, choosenode, algebra; timeout)
end

function alphasat(
    ::Type{MVHSTableau},
    α::T,
    φ::Formula,
    algebra::FiniteFLewAlgebra;
    timeout::Union{Nothing, Int} = nothing
) where {
    T<:Truth
}
    return alphasat(
        MVHSTableau,
        α,
        φ,
        algebra,
        roundrobin!,
        randombranch;
        timeout
    )
end

function alphaval(
    ::Type{MVHSTableau},
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
    x, y = Point1D.([1, 2])
    os = Vector{ManyValuedLinearOrder}()
    for δ in getdomain(algebra)
        istop(δ) && continue
        for β in getdomain(algebra)
            isbot(β) && continue
            for γ in getdomain(algebra)
                mvlt = SMatrix{2,2,FiniteTruth}(
                    [[FiniteTruth(2) β]; [γ FiniteTruth(2)]]
                )
                mveq = SMatrix{2,2,FiniteTruth}(
                    [[FiniteTruth(1) δ]; [δ FiniteTruth(1)]]
                )
                if isaManyValuedLinearOrder(mvlt, mveq, algebra)
                    push!(
                        os,
                        @inbounds ManyValuedLinearOrder(mvlt, mveq, algebra)
                    )
                end
            end
        end
    end
    metricheaps = Vector{MetricHeap}()  # Heaps to be used for node selection
    for metric ∈ metrics
        push!(metricheaps, MetricHeap(metric))
    end
    for o ∈ os
        !isaInterval(x, y, o) && continue
        i = @inbounds Interval(x, y, o)
        tableau = MVHSTableau(false, (α, φ), i, o)
        for metricheap ∈ metricheaps
            push!(heap(metricheap), MetricHeapNode(metric(metricheap), tableau))
        end
    end
    r = alphasat(metricheaps, choosenode, algebra; timeout)
    if isnothing(r)
        return r
    else
        return !r
    end
end

function alphaval(
    ::Type{MVHSTableau},
    α::T,
    φ::Formula,
    algebra::FiniteFLewAlgebra;
    timeout::Union{Nothing, Int} = nothing
) where {
    T<:Truth
}
    return alphaval(
        MVHSTableau,
        α,
        φ,
        algebra,
        roundrobin!,
        randombranch;
        timeout
    )
end
