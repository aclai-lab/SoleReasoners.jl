struct Point1D
    label::String   # Point on many-valued linear order D_1
end

Base.show(io::IO, p::Point1D) = print(io, p.label)
