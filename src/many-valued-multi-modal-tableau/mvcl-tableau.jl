using Base.Threads

"""
    mutable struct MVCLTableau <: ManyValuedMultiModalTableau
        const judgement::Bool
        const assertion::NTuple{2,Formula}
        const world::Point2D
        const frame::NTuple{2,ManyValuedLinearOrder}
        const father::Union{MVCLTableau,Nothing}
        const children::Vector{MVCLTableau}
        expanded::Bool
        closed::Bool
    end

Tableau to reason about Many-Valued Compass Logic.
"""
mutable struct MVCLTableau <: ManyValuedMultiModalTableau
    const judgement::Bool
    const assertion::NTuple{2,Formula}
    const world::Point2D
    const frame::NTuple{2,ManyValuedLinearOrder}
    const father::Union{MVCLTableau,Nothing}
    const children::Vector{MVCLTableau}
    expanded::Bool
    closed::Bool

    function MVCLTableau(
        judgement::Bool,
        assertion::NTuple{2,Formula},
        world::Point2D,
        frame::NTuple{2,ManyValuedLinearOrder}
    )
        return new(
            judgement,
            assertion,
            world,
            frame,
            nothing,
            Vector{MVCLTableau}(),
            false,
            false
        )
    end

    function MVCLTableau(
        judgement::Bool,
        assertion::NTuple{2,Formula},
        world::Point2D,
        frame::NTuple{2,ManyValuedLinearOrder},
        father::MVCLTableau
    )
        newtableau = new(
            judgement,
            assertion,
            world,
            frame,
            father,
            Vector{MVCLTableau}(),
            false,
            false
        )
        pushchild!(father, newtableau)
        return newtableau
    end
end

function worlds(::Type{MVCLTableau}, frame::NTuple{2,ManyValuedLinearOrder})
    pointsx = Point1D.([UInt8(1):UInt8(cardinality(frame[1]))]...)
    pointsy = Point1D.([UInt8(1):UInt8(cardinality(frame[2]))]...)
    return map(
        x->(Point2D(x[1], x[2])), Iterators.product(pointsx, pointsy)
    )
end

function newframes(
    t::MVCLTableau,
    algebra::FiniteFLewAlgebra;
    timeout=nothing,
    t0=nothing
)
    ox, oy = frame(t)
    nx, ny = cardinality.([ox, oy])
    osx, osy = Vector{ManyValuedLinearOrder}.([[ox], [oy]])
    lock = Threads.ReentrantLock();
    combsx = unique(
        [
            (
                collect.(
                    permutations.(
                        with_replacement_combinations(getdomain(algebra), nx)
                    )
                )...
            )...
        ]
    )
    @threads for ltzcomb in combsx
        for gtzcomb in combsx
            for eqzcomb in combsx
                if !isnothing(timeout) &&
                    (time_ns()-t0)/1e9 > timeout
                    return nothing
                end
                mvlt = Matrix(undef, nx+1, nx+1)
                mvlt[1:nx, 1:nx] = ox.mvlt
                mvlt[1:nx, nx+1] = ltzcomb
                mvlt[nx+1, 1:nx] = gtzcomb
                mvlt[nx+1, nx+1] = FiniteTruth(2)
                mvlt = SMatrix{nx+1,nx+1,FiniteTruth}(mvlt)
                mveq = Matrix(undef, nx+1, nx+1)
                mveq[1:nx, 1:nx] = ox.mveq
                mveq[1:nx, nx+1] = eqzcomb
                mveq[nx+1, 1:nx] = eqzcomb
                mveq[nx+1, nx+1] = FiniteTruth(1)
                mveq = SMatrix{nx+1,nx+1,FiniteTruth}(mveq)
                if isaManyValuedLinearOrder(mvlt, mveq, algebra)
                    oz = @inbounds ManyValuedLinearOrder(mvlt, mveq, algebra)
                    @lock lock push!(osx, oz)
                end
            end
        end
    end
    combsy = unique(
        [
            (
                collect.(
                    permutations.(
                        with_replacement_combinations(getdomain(algebra), ny)
                    )
                )...
            )...
        ]
    )
    @threads for ltzcomb in combsy
        for gtzcomb in combsy
            for eqzcomb in combsy
                if !isnothing(timeout) &&
                    (time_ns()-t0)/1e9 > timeout
                    return nothing
                end
                mvlt = Matrix(undef, ny+1, ny+1)
                mvlt[1:ny, 1:ny] = oy.mvlt
                mvlt[1:ny, ny+1] = ltzcomb
                mvlt[ny+1, 1:ny] = gtzcomb
                mvlt[ny+1, ny+1] = FiniteTruth(2)
                mvlt = SMatrix{ny+1,ny+1,FiniteTruth}(mvlt)
                mveq = Matrix(undef, ny+1, ny+1)
                mveq[1:ny, 1:ny] = oy.mveq
                mveq[1:ny, ny+1] = eqzcomb
                mveq[ny+1, 1:ny] = eqzcomb
                mveq[ny+1, ny+1] = FiniteTruth(1)
                mveq = SMatrix{ny+1,ny+1,FiniteTruth}(mveq)
                if isaManyValuedLinearOrder(mvlt, mveq, algebra)
                    oz = @inbounds ManyValuedLinearOrder(mvlt, mveq, algebra)
                    @lock lock push!(osy, oz)
                end
            end
        end
    end
    return Iterators.product(osx, osy)
end

function alphasat(
    ::Type{MVCLTableau},
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
    p = Point2D(Point1D(1), Point1D(1))
    ox = ManyValuedLinearOrder(
        SMatrix{1,1}([FiniteTruth(2)]),
        SMatrix{1,1}([FiniteTruth(1)]),
        algebra
    )
    oy = ManyValuedLinearOrder(
        SMatrix{1,1}([FiniteTruth(2)]),
        SMatrix{1,1}([FiniteTruth(1)]),
        algebra
    )
    tableau = MVCLTableau(true, (α, φ), p, (ox, oy))
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
    ::Type{MVCLTableau},
    α::T,
    φ::Formula,
    algebra::FiniteFLewAlgebra;
    timeout::Union{Nothing, Int} = nothing
) where {
    T<:Truth
}
    return alphasat(
        MVCLTableau,
        α,
        φ,
        algebra,
        roundrobin!,
        randombranch;
        timeout
    )
end

function alphaval(
    ::Type{MVCLTableau},
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
    p = Point2D(Point1D(1), Point1D(1))
    ox = ManyValuedLinearOrder(
        SMatrix{1,1}([FiniteTruth(2)]),
        SMatrix{1,1}([FiniteTruth(1)]),
        algebra
    )
    oy = ManyValuedLinearOrder(
        SMatrix{1,1}([FiniteTruth(2)]),
        SMatrix{1,1}([FiniteTruth(1)]),
        algebra
    )
    tableau = MVCLTableau(false, (α, φ), p, (ox, oy))
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
    ::Type{MVCLTableau},
    α::T,
    φ::Formula,
    algebra::FiniteFLewAlgebra;
    timeout::Union{Nothing, Int} = nothing
) where {
    T<:Truth
}
    return alphaval(
        MVCLTableau,
        α,
        φ,
        algebra,
        roundrobin!,
        randombranch;
        timeout
    )
end
