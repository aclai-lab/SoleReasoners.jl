using SoleLogics: Formula, syntaxstring

"""
    abstract type ManyValuedMultiModalTableau end

Tableau to reason about Many-Valued Multi-Modal Logic.
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
    isroot(t::T) where {T<:ManyValuedMultiModalTableau}

Return `true` if a tableu `t` is the root of the tableau, `false` otherwise.
"""
isroot(t::T) where {T<:ManyValuedMultiModalTableau} = isnothing(t.father)

"""
    expand!(t::T) where {T<:ManyValuedMultiModalTableau}

Set the `expanded` flag to `true`.
"""
expand!(t::T) where {T<:ManyValuedMultiModalTableau} = t.expanded = true

"""
    close!(t::T) where {T<:ManyValuedMultiModalTableau}

Set the `closed` flag to `true`.
"""
close!(t::T) where {T<:ManyValuedMultiModalTableau} = t.closed = true

"""
    pushchild!(father::T, child::T) where {T<:ManyValuedMultiModalTableau}

Push new `child` tableau to the `children` of `father` tableau.
"""
function pushchild!(father::T, child::T) where {T<:ManyValuedMultiModalTableau}
    push!(father.children, child)
end
