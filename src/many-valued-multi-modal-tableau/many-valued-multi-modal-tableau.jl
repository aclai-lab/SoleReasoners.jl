using SoleLogics: Formula, syntaxstring

"""
    abstract type ManyValuedMultiModalTableau <: AbstractTableau end

Tableau to reason about Many-Valued Multi-Modal Logic; a subtype of
`ManyValuedMultiModalTableau` is expected to have at least a `judgement`, an
`assertion`, a `world`, a `frame`, a `father`, an array of `children`, and two
flags `expanded` and `closed`.
"""
abstract type ManyValuedMultiModalTableau <: AbstractTableau end

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
    worlds(
        ::Type{T},
        frame::Union{ManyValuedLinearOrder, NTuple{2, ManyValuedLinearOrder}}
    ) where {
        T<:ManyValuedMultiModalTableau
    }

Return all the worlds in the `frame` associated with a tableau `t`.
"""
function worlds(
    ::Type{T},
    frame::Union{ManyValuedLinearOrder, NTuple{2, ManyValuedLinearOrder}}
) where {
    T<:ManyValuedMultiModalTableau
}
    error("Please, specify how to return all worlds in `frame(t::$T)`")
end

"""
    newframes(
    ::Type{T},
    algebra::FiniteFLewAlgebra
) where {
    T<:ManyValuedMultiModalTableau
}

Return all the new possible `frame`s for a tableau of type `T`.
"""
function newframes(
    t::T,
    algebra::FiniteFLewAlgebra
) where {
    T<:ManyValuedMultiModalTableau
}
    error("Please, specify how to generate new frames for `t::$T`")
end

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
