struct Interval
    x::Point1D  # Point on many-valued linear order D_1
    y::Point1D  # Point on many-valued linear order D_1
end

Base.show(io::IO, i::Interval) = print(io, "[$(i.x),$(i.y)]")
