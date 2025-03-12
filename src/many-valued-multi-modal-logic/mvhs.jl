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
end

"""
    show(io::IO, p::Point2D)

An `Interval` is printed as `[xi,xj]`, where `i` and `j` are the indexes of the
`Point1D`s `p1` and `p2` in the domain associated with the many-valued linear
order they belong to.
"""
Base.show(io::IO, i::Interval) = print(io, "[x$(i.p1.index),x$(i.p2.index)]")
