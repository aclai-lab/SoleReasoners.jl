"""
    struct Rectangle
        ix::Interval
        iy::Interval
    end

A `Rectangle` is represented by an `Interval` on a many-valued linear order `Dx`
and another `Interval` on a many-valued linear order `Dy`.
"""
struct Rectangle
    ix::Interval
    iy::Interval
end

"""
A `Rectangle` is printed as `([xi,xj],[yk,yl])`, where `i` and `j` are the
indexes of the `Point1D`s of the first `Interval` in the domain associated with
the many-valued linear order `Dx` and `k` and `l` are the indexes of the
`Point1D`s of the second `Interval` in the domain associated with the
many-valued linear order `Dy`.
"""
function Base.show(io::IO, r::Rectangle)
    print(
        io,
        "(" *
            "[x$(r.ix.p1.index),x$(r.ix.p2.index)]," *
            "[y$(r.iy.p1.index),y$(r.iy.p2.index)]" *
        ")"
    )
end
