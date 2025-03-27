"""
    mutable struct MVHSTableau <: ManyValuedMultiModalTableau
        const judgement::Bool
        const assertion::NTuple{2,Formula}
        const world::Interval
        const frame::ManyValuedLinearOrder
        const father::Union{MVHSTableau,Nothing}
        const children::Vector{MVHSTableau}
        expanded::Bool
        closed::Bool
    end

Tableau to reason about Many-Valued Halpern and Shoham's modal logic of time
intervals.
"""
mutable struct MVHSTableau <: ManyValuedMultiModalTableau
    const judgement::Bool
    const assertion::NTuple{2,Formula}
    const world::Interval
    const frame::ManyValuedLinearOrder
    const father::Union{MVHSTableau,Nothing}
    const children::Vector{MVHSTableau}
    expanded::Bool
    closed::Bool

    function MVHSTableau(
        judgement::Bool,
        assertion::NTuple{2,Formula},
        world::Interval,
        frame::ManyValuedLinearOrder
    )
        return new(
            judgement,
            assertion,
            world,
            frame,
            nothing,
            Vector{MVHSTableau}(),
            false,
            false
        )
    end

    function MVHSTableau(
        judgement::Bool,
        assertion::NTuple{2,Formula},
        world::Interval,
        frame::ManyValuedLinearOrder,
        father::MVHSTableau
    )
        return new(
            judgement,
            assertion,
            world,
            frame,
            father,
            Vector{MVHSTableau}(),
            false,
            false
        )
    end
end
