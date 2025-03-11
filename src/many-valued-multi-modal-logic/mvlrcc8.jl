struct Rectangle
    xy::Interval    # Interval on many-valued linear order D_1
    zt::Interval    # Interval on many-valued linear order D_2
end

Base.show(io::IO, r::Rectangle) = print(io, "($(r.xy),$(r.zt))")
