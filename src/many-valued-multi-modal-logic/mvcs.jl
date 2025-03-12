using SoleLogics: CL_N, CL_S, CL_E, CL_W

"""
    struct Point2D
        px::Point1D
        py::Point1D
    end

A `Point2D` is represented by a `Point1D` in a many-valued linear order `Dx` and
another `Point1D` in a many-valued linear order `Dy`.
"""
struct Point2D
    px::Point1D
    py::Point1D
end

"""
    show(io::IO, p::Point2D)

A `Point2D` is printed as `(xi,yj)`, where `i` is the index of the `Point1D` in
the domain associated with the many-valued linear order `Dx`, and `j` is the
index of the `Point1D` in the domain associated with the many-valued linear
order `Dy`.
"""
Base.show(io::IO, p::Point2D) = print(io, "(x$(p.px.index),y$(p.py.index))")

"""
    function mveval(
        ::typeof(CL_N),
        p1::Point2D,
        p2::Point2D,
        (ox,oy)::NTuple{2,ManyValuedLinearOrder}
    )
Many-valued evaluation function p1Rp2 = ̃=(p1x,p2x)⋅̃<(p1y,p2y) for relation
R=CL_N in many-valued linear orders `ox` and `oy` (how much `p2` is norther than
`p1`).
"""
function mveval(
    ::typeof(CL_N),
    p1::Point2D,
    p2::Point2D,
    (ox,oy)::NTuple{2,ManyValuedLinearOrder}
)
    return ox.algebra.monoid(mveq(p1.px, p2.px, ox), mvlt(p1.py, p2.py, oy))
end

"""
    function mveval(
        ::typeof(CL_S),
        p1::Point2D,
        p2::Point2D,
        (ox,oy)::NTuple{2,ManyValuedLinearOrder}
    )
Many-valued evaluation function p1Rp2 = ̃=(p1x,p2x)⋅̃<(p2y,p1y) for relation
R=CL_S in many-valued linear orders `ox` and `oy` (how much `p2` is souther than
`p1`).
"""
function mveval(
    ::typeof(CL_S),
    p1::Point2D,
    p2::Point2D,
    (ox,oy)::NTuple{2,ManyValuedLinearOrder}
)
    return ox.algebra.monoid(mveq(p1.px, p2.px, ox), mvlt(p2.py, p1.py, oy))
end

"""
    function mveval(
        ::typeof(CL_E),
        p1::Point2D,
        p2::Point2D,
        (ox,oy)::NTuple{2,ManyValuedLinearOrder}
    )
Many-valued evaluation function p1Rp2 = ̃<(p1x,p2x)⋅̃=(p1y,p2y) for relation
R=CL_E in many-valued linear orders `ox` and `oy` (how much `p2` is easter than
`p1`).
"""
function mveval(
    ::typeof(CL_E),
    p1::Point2D,
    p2::Point2D,
    (ox,oy)::NTuple{2,ManyValuedLinearOrder}
)
    return ox.algebra.monoid(mvlt(p1.px, p2.px, ox), mveq(p1.py, p2.py, oy))
end

"""
    function mveval(
        ::typeof(CL_W),
        p1::Point2D,
        p2::Point2D,
        (ox,oy)::NTuple{2,ManyValuedLinearOrder}
    )
Many-valued evaluation function p1Rp2 = ̃<(p2x,p1x)⋅̃=(p1y,p2y) for relation
R=CL_W in many-valued linear orders `ox` and `oy` (how much `p2` is wester than
`p1`).
"""
function mveval(
    ::typeof(CL_W),
    p1::Point2D,
    p2::Point2D,
    (ox,oy)::NTuple{2,ManyValuedLinearOrder}
)
    return ox.algebra.monoid(mvlt(p2.px, p1.px, ox), mveq(p1.py, p2.py, oy))
end
