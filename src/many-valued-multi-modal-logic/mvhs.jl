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

Base.show(io::IO, i::Interval) = print(io, "[x$(i.p1.index),x$(i.p2.index)]")
