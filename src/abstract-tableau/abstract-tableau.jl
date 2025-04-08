import Base: isempty, pop!, push!

"""
    abstract type AbstractTableau end

Abstract type for all tableaux structures.

All tableaux structures are recursive structures resembling a tree structure.
Each subtype `T` where `T<:AbstractTableau` is expected to have at least a
field `faher` of the same type `T` (or `Nothing` in case it is the root), a
field `children` comprising a vector of elements of type `T`, and two flags
`expanded` and `closed` of type `Bool` claiming if the node has been expanded
(resp. closed) or not.
"""
abstract type AbstractTableau end

"""
    father(t::T) where {T<:AbstractTableau}

Return the father of a tableu `t`.
"""
father(t::T) where {T<:AbstractTableau} = t.father

"""
    children(t::T) where {T<:AbstractTableau}

Return the vector of children of a tableu `t`.
"""
children(t::T) where {T<:AbstractTableau} = t.children

"""
    expanded(t::T) where {T<:AbstractTableau}

Return `true` if a tableu `t` has already been expanded, `false` otherwise.
"""
expanded(t::T) where {T<:AbstractTableau} = t.expanded

"""
    closed(t::T) where {T<:AbstractTableau}

Return `true` if a tableu `t` has already been closed, `false` otherwise.
"""
closed(t::T) where {T<:AbstractTableau} = t.closed

"""
    isroot(t::T) where {T<:AbstractTableau}

Return `true` if a tableu `t` is the root of the tableau, `false` otherwise.
"""
isroot(t::T) where {T<:AbstractTableau} = isnothing(t.father)

"""
    isleaf(t::T) where {T<:AbstractTableau}

Return `true` if a tableu `t` is a leaf of the tableau, `false` otherwise.
"""
isleaf(t::T) where {T<:AbstractTableau} = isempty(t.children)

"""
    expand!(t::T) where {T<:AbstractTableau}

Set the `expanded` flag to `true`.
"""
expand!(t::T) where {T<:AbstractTableau} = t.expanded = true

"""
    findexpansionnode(t::T) where {T<:AbstractTableau}

Search for the node to be expanded recursevely scanning the ancestors of `t`.
"""
function findexpansionnode(t::T) where {T<:AbstractTableau}
    isroot(t) || expanded(t.father) ? t : findexpansionnode(t.father)
end

"""
    findleaves(t::T) where {T<:AbstractTableau}

Find all leaves descendants of `t`.
"""
function findleaves(leaves::Vector{T}, t::T) where {T<:AbstractTableau}
    if isempty(t.children)
        push!(leaves, t)
    else
        for child in t.children
            findleaves(leaves, child)
        end
    end
    return leaves
end
function findleaves(t::T) where {T<:AbstractTableau}
    findleaves(Vector{T}(), t)
end

"""
    close!(t::T) where {T<:AbstractTableau}

Set the `closed` flag of `t` to true and recursevely close all its descendants;
if `t` is not the root of the tableau, also remove it from the list of children
of its `father` and if `t` does not have any simblings recursevely close it.
"""
function close!(t::T) where {T<:AbstractTableau}
    t.closed = true
    if !isroot(t) && !closed(t.father)
        filter!(e->e≠t, t.father.children)
        if isempty(t.father.children)
            close!(t.father)
        end
    end
    while !isempty(t.children)
        c = pop!(t.children)
        close!(c)
    end
end

"""
    pushchild!(father::T, child::T) where {T<:AbstractTableau}

Push new `child` tableau to the `children` of `father` tableau.
"""
function pushchild!(father::T, child::T) where {T<:AbstractTableau}
    push!(father.children, child)
end

"""
    show(io::IO, _::T) where {T<:AbstractTableau}

Method to be overwritten with the signature of a specific tableaux structure.
"""
function Base.show(io::IO, _::T) where {T<:AbstractTableau}
    error(io, "Please, provide a `show` method for $T")
end
