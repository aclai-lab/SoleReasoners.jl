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

# Helper
function isaInterval(p1::Int, p2::Int, o::ManyValuedLinearOrder)
    return isaInterval(Point1D(p1), Point1D(p2), o)
end

"""
    checkInterval(p1::Point1D, p2::Point1D, o::ManyValuedLinearOrder)

Check if a two `Point1D`s `p1` and `p1` form an interval in the many-valued
linear order `o`, i.e., ̃<(p1,p2) ≻ ⊥. 
"""
function checkInterval(p1::Point1D, p2::Point1D, o::ManyValuedLinearOrder)
    if !isaInterval(p1, p2, o)
        error("`p1` and `p2` do not form an `Interval` in `o`")
    end
end

# Helper
function checkInterval(p1::Int, p2::Int, o::ManyValuedLinearOrder)
    return checkInterval(Point1D(p1), Point1D(p2), o)
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

    @inline function Interval(
        p1::Int,
        p2::Int,
        o::ManyValuedLinearOrder
    )
        @boundscheck checkInterval(p1, p2, o)
        return new(Point1D(p1), Point1D(p2))
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
Many-valued evaluation function i1Ri2 = ̃=(i1p2,i2p1) for relation R=HS_A in
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

"""
    function mveval(
        ::typeof(HS_L),
        i1::Interval,
        i2::Interval,
        o::ManyValuedLinearOrder
    )
Many-valued evaluation function i1Ri2 = ̃<(i1p2,i2p1) for relation R=HS_L in
many-valued linear order `o` (how much `i2` is later than `i1`).
"""
function mveval(
    ::typeof(HS_L),
    i1::Interval,
    i2::Interval,
    o::ManyValuedLinearOrder
)
    return mvlt(i1.p2, i2.p1, o)
end

"""
    function mveval(
        ::typeof(HS_B),
        i1::Interval,
        i2::Interval,
        o::ManyValuedLinearOrder
    )
Many-valued evaluation function i1Ri2 = ̃=(i1p1,i2p1) ⋅ ̃<(i2p2,i1p2) for relation
R=HS_B in many-valued linear order `o` (how much `i2` is at the begin of `i1`).
"""
function mveval(
    ::typeof(HS_B),
    i1::Interval,
    i2::Interval,
    o::ManyValuedLinearOrder
)
    return o.algebra.monoid(mveq(i1.p1, i2.p1, o), mvlt(i2.p2, i1.p2, o))
end

"""
    function mveval(
        ::typeof(HS_E),
        i1::Interval,
        i2::Interval,
        o::ManyValuedLinearOrder
    )
Many-valued evaluation function i1Ri2 = ̃<(i1p1,i2p1) ⋅ ̃=(i1p2,i2p2) for relation
R=HS_E in many-valued linear order `o` (how much `i2` is at the end of `i1`).
"""
function mveval(
    ::typeof(HS_E),
    i1::Interval,
    i2::Interval,
    o::ManyValuedLinearOrder
)
    return o.algebra.monoid(mvlt(i1.p1, i2.p1, o), mveq(i1.p2, i2.p2, o))
end

"""
    function mveval(
        ::typeof(HS_D),
        i1::Interval,
        i2::Interval,
        o::ManyValuedLinearOrder
    )
Many-valued evaluation function i1Ri2 = ̃<(i1p1,i2p1) ⋅ ̃<(i2p2,i1p2) for relation
R=HS_D in many-valued linear order `o` (how much `i2` is during `i1`).
"""
function mveval(
    ::typeof(HS_D),
    i1::Interval,
    i2::Interval,
    o::ManyValuedLinearOrder
)
    return o.algebra.monoid(mvlt(i1.p1, i2.p1, o), mvlt(i2.p2, i1.p2, o))
end

"""
    function mveval(
        ::typeof(HS_O),
        i1::Interval,
        i2::Interval,
        o::ManyValuedLinearOrder
    )
Many-valued evaluation function
i1Ri2 = ̃<(i1p1,i2p1) ⋅ ̃<(i2p1,i1p2) ⋅ ̃<(i1p2, i2p2) for relation R=HS_O in
many-valued linear order `o` (how much `i2` is overlapping `i1`).
"""
function mveval(
    ::typeof(HS_O),
    i1::Interval,
    i2::Interval,
    o::ManyValuedLinearOrder
)
    return o.algebra.monoid(
        o.algebra.monoid(mvlt(i1.p1, i2.p1, o), mvlt(i2.p1, i1.p2, o)),
        mvlt(i1.p2, i2.p2, o)
    )
end

"""
    function mveval(
        ::typeof(HS_Ai),
        i1::Interval,
        i2::Interval,
        o::ManyValuedLinearOrder
    )
Many-valued evaluation function i1Ri2 = ̃=(i2p2,i1p1) for relation R=HS_Ai in
many-valued linear order `o` (how much `i1` is after `i2`).
"""
function mveval(
    ::typeof(HS_Ai),
    i1::Interval,
    i2::Interval,
    o::ManyValuedLinearOrder
)
    return mveq(i2.p2, i1.p1, o)
end

"""
    function mveval(
        ::typeof(HS_Li),
        i1::Interval,
        i2::Interval,
        o::ManyValuedLinearOrder
    )
Many-valued evaluation function i1Ri2 = ̃<(i2p2,i1p1) for relation R=HS_Li in
many-valued linear order `o` (how much `i1` is later than `i2`).
"""
function mveval(
    ::typeof(HS_Li),
    i1::Interval,
    i2::Interval,
    o::ManyValuedLinearOrder
)
    return mvlt(i2.p2, i1.p1, o)
end

"""
    function mveval(
        ::typeof(HS_Bi),
        i1::Interval,
        i2::Interval,
        o::ManyValuedLinearOrder
    )
Many-valued evaluation function i1Ri2 = ̃=(i1p1,i2p1) ⋅ ̃<(i1p2,i2p2) for relation
R=HS_Bi in many-valued linear order `o` (how much `i1` is at the begin of `i2`).
"""
function mveval(
    ::typeof(HS_Bi),
    i1::Interval,
    i2::Interval,
    o::ManyValuedLinearOrder
)
    return o.algebra.monoid(mveq(i1.p1, i2.p1, o), mvlt(i1.p2, i2.p2, o))
end

"""
    function mveval(
        ::typeof(HS_Ei),
        i1::Interval,
        i2::Interval,
        o::ManyValuedLinearOrder
    )
Many-valued evaluation function i1Ri2 = ̃<(i2p1,i1p1) ⋅ ̃=(i1p2,i2p2) for relation
R=HS_Ei in many-valued linear order `o` (how much `i1` is at the end of `i2`).
"""
function mveval(
    ::typeof(HS_Ei),
    i1::Interval,
    i2::Interval,
    o::ManyValuedLinearOrder
)
    return o.algebra.monoid(mvlt(i2.p1, i1.p1, o), mveq(i1.p2, i2.p2, o))
end

"""
    function mveval(
        ::typeof(HS_Di),
        i1::Interval,
        i2::Interval,
        o::ManyValuedLinearOrder
    )
Many-valued evaluation function i1Ri2 = ̃<(i2p1,i1p1) ⋅ ̃<(i1p2,i2p2) for relation
R=HS_Di in many-valued linear order `o` (how much `i1` is during `i2`).
"""
function mveval(
    ::typeof(HS_Di),
    i1::Interval,
    i2::Interval,
    o::ManyValuedLinearOrder
)
    return o.algebra.monoid(mvlt(i2.p1, i1.p1, o), mvlt(i1.p2, i2.p2, o))
end

"""
    function mveval(
        ::typeof(HS_Oi),
        i1::Interval,
        i2::Interval,
        o::ManyValuedLinearOrder
    )
Many-valued evaluation function
i1Ri2 = ̃<(i2p1,i1p1) ⋅ ̃<(i1p1,i2p2) ⋅ ̃<(i2p2, i1p2) for relation R=HS_Oi in
many-valued linear order `o` (how much `i1` is overlapping `i2`).
"""
function mveval(
    ::typeof(HS_Oi),
    i1::Interval,
    i2::Interval,
    o::ManyValuedLinearOrder
)
    return o.algebra.monoid(
        o.algebra.monoid(mvlt(i2.p1, i1.p1, o), mvlt(i1.p1, i2.p2, o)),
        mvlt(i2.p2, i1.p2, o)
    )
end
