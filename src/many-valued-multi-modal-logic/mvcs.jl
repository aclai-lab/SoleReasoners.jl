struct Point2D
    x::Point1D  # Point on many-valued linear order D_1
    y::Point1D  # Point on many-valued linear order D_2
end

Base.show(io::IO, p::Point2D) = print(io, "($(p.x),$(p.y))")
