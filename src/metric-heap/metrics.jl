using Random: rand, Xoshiro

"""
    randombranch(_::T) where {T<:AbstractTableau}

`metric` assigning a random weight to each node when pushing it into the heaps.
It leverages `Xoshiro` as pseudo-random generator with random seed.

For deterministic execution (i.e., experimental environments), it is advised to
reimplement a similar custom function specifying a seed for the generator, such
as:
    rng = Xoshiro(42)
    customrandombranch(_::T) where {T<:AbstractTableau} = rand(rng, Int)
Note that the `rng` is defined outside of the function body; otherwise, it
produces always the same value.
"""
function randombranch(_::T) where {T<:AbstractTableau}
    return rand(Xoshiro(), Int)
end

"""
    distancefromroot(t::T) where {T<:AbstractTableau}

`metric` assignign to each node its distance from the root giving priority to
smaller distances (i.e., breadth-first search).
"""
function distancefromroot(t::T) where {T<:AbstractTableau}
    distance = 0;
    while !isroot(t)
        distance += 1
        t = father(t)
    end
    return distance
end

"""
    inversedistancefromroot(t::T) where {T<:AbstractTableau}

`metric` assignign to each node its distance from the root giving priority to
larger distances (i.e., breadth-first search).
"""
function inversedistancefromroot(t::T) where {T<:AbstractTableau}
    distance = 0;
    while !isroot(t)
        distance += 1
        t = father(t)
    end
    return -distance
end
