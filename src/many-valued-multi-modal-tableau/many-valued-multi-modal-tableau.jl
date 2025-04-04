using SoleLogics: Formula, syntaxstring

"""
    abstract type ManyValuedMultiModalTableau end

Tableau to reason about Many-Valued Multi-Modal Logic; a subtype of
`ManyValuedMultiModalTableau` is expected to have at least a `judgement`, an
`assertion`, a 'world`, a `frame`, a `father`, an array of `children`, and two
flags `expanded` and `closed`.
"""
abstract type ManyValuedMultiModalTableau end

"""
    show(io::IO, t::T) where {T<:ManyValuedMultiModalTableau}

A `ManyValuedMultiModalTableau` is printed as a decoration `Q(α⪯φ,w,F)` or
`Q(φ⪯α,w,F)` where `Q` is a judgement, `α⪯φ` and `φ⪯α` are assertions on a
world `w`, and `F` is a frame represented by either a `ManyValuedLinearOrder`
or a tuple of two `ManyValuedLinearOrder`s.
"""
function Base.show(io::IO, t::T) where {T<:ManyValuedMultiModalTableau}
    print(
        io,
        "$(t.judgement)(" *
        "$(syntaxstring(t.assertion[1]))" *
        " ⪯ " *
        "$(syntaxstring(t.assertion[2])), $(t.world), F)"
    )
end

"""
    judgement(t::T) where {T<:ManyValuedMultiModalTableau}

Return the judgement (either true or false) associated with the tableu `t`.
"""
judgement(t::T) where {T<:ManyValuedMultiModalTableau} = t.judgement

"""
    assertion(t::T) where {T<:ManyValuedMultiModalTableau}

Return the assertion associated with a tableu `t`.
"""
assertion(t::T) where {T<:ManyValuedMultiModalTableau} = t.assertion

"""
    world(t::T) where {T<:ManyValuedMultiModalTableau}

Return the world associated with a tableu `t`.
"""
world(t::T) where {T<:ManyValuedMultiModalTableau} = t.world

"""
    frame(t::T) where {T<:ManyValuedMultiModalTableau}

Return the frame associated with a tableu `t`.
"""
frame(t::T) where {T<:ManyValuedMultiModalTableau} = t.frame

"""
    father(t::T) where {T<:ManyValuedMultiModalTableau}

Return the father of a tableu `t`.
"""
father(t::T) where {T<:ManyValuedMultiModalTableau} = t.father

"""
    children(t::T) where {T<:ManyValuedMultiModalTableau}

Return the vector of children of a tableu `t`.
"""
children(t::T) where {T<:ManyValuedMultiModalTableau} = t.children

"""
    expanded(t::T) where {T<:ManyValuedMultiModalTableau}

Return `true` if a tableu `t` has already been expanded, `false` otherwise.
"""
expanded(t::T) where {T<:ManyValuedMultiModalTableau} = t.expanded

"""
    closed(t::T) where {T<:ManyValuedMultiModalTableau}

Return `true` if a tableu `t` has already been closed, `false` otherwise.
"""
closed(t::T) where {T<:ManyValuedMultiModalTableau} = t.closed

"""
    pushchild!(father::T, child::T) where {T<:ManyValuedMultiModalTableau}

Push new `child` tableau to the `children` of `father` tableau.
"""
function pushchild!(father::T, child::T) where {T<:ManyValuedMultiModalTableau}
    push!(father.children, child)
end

"""
    isroot(t::T) where {T<:ManyValuedMultiModalTableau}

Return `true` if a tableu `t` is the root of the tableau, `false` otherwise.
"""
isroot(t::T) where {T<:ManyValuedMultiModalTableau} = isnothing(t.father)

"""
    isleaf(t::T) where {T<:ManyValuedMultiModalTableau}

Return `true` if a tableu `t` is a leaf of the tableau, `false` otherwise.
"""
isleaf(t::T) where {T<:ManyValuedMultiModalTableau} = isempty(t.children)

"""
    expand!(t::T) where {T<:ManyValuedMultiModalTableau}

Set the `expanded` flag to `true`.
"""
expand!(t::T) where {T<:ManyValuedMultiModalTableau} = t.expanded = true

"""
    findexpansionnode(t::T) where {T<:ManyValuedMultiModalTableau}

Search for the node to be expanded recursevely scanning the ancestors of `t`.
"""
function findexpansionnode(t::T) where {T<:ManyValuedMultiModalTableau}
    isroot(t) || expanded(t.father) ? t : findexpansionnode(t.father)
end

"""
    findleaves(t::T) where {T<:ManyValuedMultiModalTableau}

Find all leaves descendants of `t`.
"""
function findleaves(
    leaves::Vector{T},
    t::T
) where {
    T<:ManyValuedMultiModalTableau
}
    if isempty(t.children)
        push!(leaves, t)
    else
        for child in t.children
            findleaves(leaves, child)
        end
    end
    return leaves
end
function findleaves(t::T) where {T<:ManyValuedMultiModalTableau}
    findleaves(Vector{T}(), t)
end

"""
    close!(t::T) where {T<:ManyValuedMultiModalTableau}

Set the `closed` flag of `t` to true and recursevely close all its descendants;
if `t` is not the root of the tableau, also remove it from the list of children
of its `father` and if `t` does not have any simblings recursevely close it.
"""
function close!(t::T) where {T<:ManyValuedMultiModalTableau}
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
