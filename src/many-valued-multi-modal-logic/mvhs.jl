using SoleLogics: HS_A, HS_L, HS_B, HS_E, HS_D, HS_O
using SoleLogics: HS_Ai, HS_Li, HS_Bi, HS_Ei, HS_Di, HS_Oi

"""
    isaInterval(p1::Point1D, p2::Point1D, o::ManyValuedLinearOrder)

Return `true` if a two `Point1D`s `p1` and `p1` form an interval in the
many-valued linear order `o`, i.e., ̃<(p1,p2) ≻ ⊥; return `false` otherwise.
"""
function isaInterval(p1::Point1D, p2::Point1D, o::ManyValuedLinearOrder)
    return !isbot(mvlt(p1, p2, o))
end

"""
    checkInterval(p1::Point1D, p2::Point1D, o::ManyValuedLinearOrder)

Check if a two `Point1D`s `p1` and `p1` form an interval in the many-valued
linear order `o`, i.e., ̃<(p1,p2) ≻ ⊥. 
"""
function checkInterval(p1::Point1D, p2::Point1D, o::ManyValuedLinearOrder)
    if !isaInterval(p1, p2, o)
        error("`p1` and `p2` do not form an `Interval` in `o`.")
    end
end

"""
    struct Interval
        p1::Point1D
        p1::Point1D
    end

An `Interval` is represented by two `Point1D`s in the same many-valued linear
order.
"""
struct Interval
    p1::Point1D
    p2::Point1D

    @inline function Interval(
        p1::Point1D,
        p2::Point1D,
        o::ManyValuedLinearOrder
    )
        @boundscheck checkInterval(p1, p2, o)
        return new(p1, p2)
    end
end

"""
    show(io::IO, p::Interval)

An `Interval` is printed as `[xi,xj]`, where `i` and `j` are the indexes of the
`Point1D`s `p1` and `p2` in the domain associated with the many-valued linear
order they belong to.
"""
Base.show(io::IO, i::Interval) = print(io, "[x$(i.p1.index),x$(i.p2.index)]")

"""
    function mveval(
        ::typeof(HS_A),
        i1::Interval,
        i2::Interval,
        o::ManyValuedLinearOrder
    )
Many-valued evaluation function p1Rp2 = ̃=(i1p2,i2p1) for relation R=HS_A in
many-valued linear order `o` (how much `i2` is after `i1`).
"""
function mveval(
    ::typeof(HS_A),
    i1::Interval,
    i2::Interval,
    o::ManyValuedLinearOrder
)
    return mveq(i1.p2, i2.p1, o)
end
