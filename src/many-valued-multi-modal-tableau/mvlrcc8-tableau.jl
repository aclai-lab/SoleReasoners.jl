using Base.Threads

"""
Tableau to reason about Many-Valued Lutz and Wolter's modal logic of topological
relations with rectangular areas aligned with the axes.
"""
mutable struct MVLRCC8Tableau <: ManyValuedMultiModalTableau
    const judgement::Bool
    const assertion::NTuple{2,Formula}
    const world::Rectangle
    const frame::NTuple{2,ManyValuedLinearOrder}
    const father::Union{MVLRCC8Tableau,Nothing}
    const children::Vector{MVLRCC8Tableau}
    expanded::Bool
    closed::Bool

    function MVLRCC8Tableau(
        judgement::Bool,
        assertion::NTuple{2,Formula},
        world::Rectangle,
        frame::NTuple{2,ManyValuedLinearOrder}
    )
        return new(
            judgement,
            assertion,
            world,
            frame,
            nothing,
            Vector{MVLRCC8Tableau}(),
            false,
            false
        )
    end

    function MVLRCC8Tableau(
        judgement::Bool,
        assertion::NTuple{2,Formula},
        world::Rectangle,
        frame::NTuple{2,ManyValuedLinearOrder},
        father::MVLRCC8Tableau
    )
        newtableau =  new(
            judgement,
            assertion,
            world,
            frame,
            father,
            Vector{MVLRCC8Tableau}(),
            false,
            false
        )
        pushchild!(father, newtableau)
        return newtableau
    end
end

function worlds(::Type{MVLRCC8Tableau}, frame::NTuple{2,ManyValuedLinearOrder})
    ox, oy = frame
    pointsx = Point1D.([UInt8(1):UInt8(cardinality(ox))]...)
    pointsy = Point1D.([UInt8(1):UInt8(cardinality(oy))]...)
    intervalsx = map(
        x->(@inbounds Interval(x[1], x[2], ox)),
        Iterators.filter(
            x->isaInterval(x[1], x[2], ox),
            Iterators.product(pointsx, pointsx)
        )
    )
    intervalsy = map(
        x->(@inbounds Interval(x[1], x[2], oy)),
        Iterators.filter(
            x->isaInterval(x[1], x[2], oy),
            Iterators.product(pointsy, pointsy)
        )
    )
    return map(
        x->(Rectangle(x[1], x[2])), Iterators.product(intervalsx, intervalsy)
    )
end

function newframes(
    t::MVLRCC8Tableau,
    algebra::FiniteFLewAlgebra;
    timeout=nothing,
    t0=nothing
)
    ox, oy = frame(t)
    nx, ny = cardinality.([ox, oy])
    osx, osy = Vector{ManyValuedLinearOrder}.([[ox], [oy]])
    lock = Threads.ReentrantLock();
    zcombsx = unique(
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
    @threads for ltzcomb in zcombsx
        for gtzcomb in zcombsx
            for eqzcomb in zcombsx
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
                    tcombsx = unique(
                        [
                            (
                                collect.(
                                    permutations.(
                                        with_replacement_combinations(
                                            getdomain(algebra),
                                            nx+1
                                        )
                                    )
                                )...
                            )...
                        ]
                    )
                    for lttcomb in tcombsx
                        for gttcomb in tcombsx
                            for eqtcomb in tcombsx
                                if !isnothing(timeout) &&
                                   (time_ns()-t0)/1e9 > timeout
                                    return nothing
                                end
                                mvlt = Matrix(undef, nx+2, nx+2)
                                mvlt[1:nx+1, 1:nx+1] = oz.mvlt
                                mvlt[1:nx+1, nx+2  ] = lttcomb
                                mvlt[nx+2,   1:nx+1] = gttcomb
                                mvlt[nx+2,   nx+2  ] = FiniteTruth(2)
                                mvlt = SMatrix{nx+2,nx+2,FiniteTruth}(mvlt)
                                mveq = Matrix(undef, nx+2, nx+2)
                                mveq[1:nx+1, 1:nx+1] = oz.mveq
                                mveq[1:nx+1, nx+2  ] = eqtcomb
                                mveq[nx+2,   1:nx+1] = eqtcomb
                                mveq[nx+2,   nx+2  ] = FiniteTruth(1)
                                mveq = SMatrix{nx+2,nx+2,FiniteTruth}(mveq)
                                if isaManyValuedLinearOrder(mvlt, mveq, algebra)
                                    ot = @inbounds ManyValuedLinearOrder(
                                        mvlt,
                                        mveq,
                                        algebra
                                    )
                                    @lock lock push!(osx, ot)
                                end
                            end
                        end
                    end
                end
            end
        end
    end
    zcombsy = unique(
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
    @threads for ltzcomb in zcombsy
        for gtzcomb in zcombsy
            for eqzcomb in zcombsy
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
                    tcombsy = unique(
                        [
                            (
                                collect.(
                                    permutations.(
                                        with_replacement_combinations(
                                            getdomain(algebra),
                                            ny+1
                                        )
                                    )
                                )...
                            )...
                        ]
                    )
                    for lttcomb in tcombsy
                        for gttcomb in tcombsy
                            for eqtcomb in tcombsy
                                if !isnothing(timeout) &&
                                   (time_ns()-t0)/1e9 > timeout
                                    return nothing
                                end
                                mvlt = Matrix(undef, ny+2, ny+2)
                                mvlt[1:ny+1, 1:ny+1] = oz.mvlt
                                mvlt[1:ny+1, ny+2  ] = lttcomb
                                mvlt[ny+2,   1:ny+1] = gttcomb
                                mvlt[ny+2,   ny+2  ] = FiniteTruth(2)
                                mvlt = SMatrix{ny+2,ny+2,FiniteTruth}(mvlt)
                                mveq = Matrix(undef, ny+2, ny+2)
                                mveq[1:ny+1, 1:ny+1] = oz.mveq
                                mveq[1:ny+1, ny+2  ] = eqtcomb
                                mveq[ny+2,   1:ny+1] = eqtcomb
                                mveq[ny+2,   ny+2  ] = FiniteTruth(1)
                                mveq = SMatrix{ny+2,ny+2,FiniteTruth}(mveq)
                                if isaManyValuedLinearOrder(mvlt, mveq, algebra)
                                    ot = @inbounds ManyValuedLinearOrder(
                                        mvlt,
                                        mveq,
                                        algebra
                                    )
                                    @lock lock push!(osy, ot)
                                end
                            end
                        end
                    end
                end
            end
        end
    end
    return Iterators.product(osx, osy)
end

function alphasat(
    ::Type{MVLRCC8Tableau},
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
    x1, x2 = Point1D.([1, 2])
    y1, y2 = Point1D.([1, 2])
    osx = Vector{ManyValuedLinearOrder}()
    osy = Vector{ManyValuedLinearOrder}()
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
                        osx,
                        @inbounds ManyValuedLinearOrder(mvlt, mveq, algebra)
                    )
                    push!(
                        osy,
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
    for frame ∈ Iterators.product(osx, osy)
        !isaInterval(x1, x2, frame[1]) && continue
        !isaInterval(y1, y2, frame[2]) && continue
        ix = @inbounds Interval(x1, x2, frame[1])
        iy = @inbounds Interval(y1, y2, frame[2])
        r = Rectangle(ix, iy)
        tableau = MVLRCC8Tableau(true, (α, φ), r, frame)
        for metricheap ∈ metricheaps
            push!(heap(metricheap), MetricHeapNode(metric(metricheap), tableau))
        end
    end
    return alphasat(metricheaps, choosenode, algebra; timeout)
end

function alphasat(
    ::Type{MVLRCC8Tableau},
    α::T,
    φ::Formula,
    algebra::FiniteFLewAlgebra;
    timeout::Union{Nothing, Int} = nothing
) where {
    T<:Truth
}
    return alphasat(
        MVLRCC8Tableau,
        α,
        φ,
        algebra,
        roundrobin!,
        randombranch;
        timeout
    )
end

function alphaval(
    ::Type{MVLRCC8Tableau},
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
    x1, x2 = Point1D.([1, 2])
    y1, y2 = Point1D.([1, 2])
    osx = Vector{ManyValuedLinearOrder}()
    osy = Vector{ManyValuedLinearOrder}()
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
                        osx,
                        @inbounds ManyValuedLinearOrder(mvlt, mveq, algebra)
                    )
                    push!(
                        osy,
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
    for frame ∈ Iterators.product(osx, osy)
        !isaInterval(x1, x2, frame[1]) && continue
        !isaInterval(y1, y2, frame[2]) && continue
        ix = @inbounds Interval(x1, x2, frame[1])
        iy = @inbounds Interval(y1, y2, frame[2])
        r = Rectangle(ix, iy)
        tableau = MVLRCC8Tableau(false, (α, φ), r, frame)
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
    ::Type{MVLRCC8Tableau},
    α::T,
    φ::Formula,
    algebra::FiniteFLewAlgebra;
    timeout::Union{Nothing, Int} = nothing
) where {
    T<:Truth
}
    return alphaval(
        MVLRCC8Tableau,
        α,
        φ,
        algebra,
        roundrobin!,
        randombranch;
        timeout
    )
end
