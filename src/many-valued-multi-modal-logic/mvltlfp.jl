"""
    struct Point1D
        index::UInt8
    end

A `Point1D` is represented by its `index` in a many-valued linear order domain.
"""
struct Point1D
    index::UInt8

    function Point1D(index::UInt8)
        if index < 1 error("0 is not a valid index in Julia") end
        return new(index)
    end

    function Point1D(index::T) where {T<:Unsigned}
        return Point1D(convert(UInt8, index))
    end

    function Point1D(index::T) where {T<:Int}
        return Point1D(convert(UInt8, index))
    end
end

Base.show(io::IO, p::Point1D) = print(io, "x$(p.index)")
