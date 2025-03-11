"""
    struct Point2D
        px::Point1D
        py::Point1D
    end

A `Point2D` is represented by a `Point1D` in a many-valued linear order `D_1`
and another `Point1D` in a many-valued linear order `D_2`.
"""
struct Point2D
    px::Point1D
    py::Point1D
end

Base.show(io::IO, p::Point2D) = print(io, "(x$(p.px.index),y$(p.py.index))")
