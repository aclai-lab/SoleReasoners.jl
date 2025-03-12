using SoleLogics: LTLFP_F, LTLFP_P

"""
    struct Point1D
        index::UInt8
    end

A `Point1D` is represented by its `index` in a many-valued linear order domain.
"""
struct Point1D
    index::UInt8

    function Point1D(index::UInt8)
        if index < 1 error("0 is not a valid index in Julia") end
        return new(index)
    end

    function Point1D(index::T) where {T<:Unsigned}
        return Point1D(convert(UInt8, index))
    end

    function Point1D(index::T) where {T<:Int}
        return Point1D(convert(UInt8, index))
    end
end

"""
    show(io::IO, p::Point1D)

A `Point1D` is printed as `xi`, where `i` is its index in the domain associated
with the many-valued linear order it belongs to.
"""
Base.show(io::IO, p::Point1D) = print(io, "x$(p.index)")

"""
    mvlt(x1::Point1D, x2::Point1D, o::ManyValuedLinearOrder)

Return the value for the ̃< function between two `Point1D`s `x1` and `x2`on the
many-valued linear order `o`.
"""
function mvlt(x1::Point1D, x2::Point1D, o::ManyValuedLinearOrder)
    return o.mvlt[x1.index, x2.index]
end

"""
    mvlt(x1::Point1D, x2::Point1D, o::ManyValuedLinearOrder)

Return the value for the ̃= function between two `Point1D`s `x1` and `x2`on the
many-valued linear order `o`.
"""
function mveq(x1::Point1D, x2::Point1D, o::ManyValuedLinearOrder)
    return o.mveq[x1.index, x2.index]
end

"""
    function mveval(
        ::typeof(LTLFP_F),
        x1::Point1D,
        x2::Point1D,
        o::ManyValuedLinearOrder
    )
Many-valued evaluation function x1Rx2 = ̃<(x1,x2) for relation R=LTLFP_F in
many-valued linear order `o` (how much `x2` is in the future w.r.t. `x1`).
"""
function mveval(
    ::typeof(LTLFP_F),
    x1::Point1D,
    x2::Point1D,
    o::ManyValuedLinearOrder
)
    return mvlt(x1, x2, o)
end

"""
    function mveval(
        ::typeof(LTLFP_P),
        x1::Point1D,
        x2::Point1D,
        o::ManyValuedLinearOrder
    )
Many-valued evaluation function x1Rx2 = ̃<(x2,x1) for relation R=LTLFP_P in
many-valued linear order `o` (how much `x2` is in the past w.r.t. `x1`).
"""
function mveval(
    ::typeof(LTLFP_P),
    x1::Point1D,
    x2::Point1D,
    o::ManyValuedLinearOrder
)
    return mvlt(x2, x1, o)
end
