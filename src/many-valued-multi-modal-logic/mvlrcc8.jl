"""
    struct Rectangle
        ix::Interval
        iy::Interval
    end

A `Rectangle` is represented by an `Interval` on a many-valued linear order
`D_1` and another `Interval` on a many-valued linear order `D_2`.
"""
struct Rectangle
    ix::Interval
    iy::Interval
end

function Base.show(io::IO, r::Rectangle)
    print(
        io,
        "(" *
            "[x$(r.ix.p1.index),x$(r.ix.p2.index)]," *
            "[y$(r.iy.p1.index),y$(r.iy.p2.index)]" *
        ")"
    )
end