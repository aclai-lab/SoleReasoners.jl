"""
    mutable struct MVLTLFPTableau <: ManyValuedMultiModalTableau
        const judgement::Bool
        const assertion::NTuple{2,Formula}
        const world::Point1D
        const frame::ManyValuedLinearOrder
        const father::Union{MVLTLFPTableau,Nothing}
        const children::Vector{MVLTLFPTableau}
        expanded::Bool
        closed::Bool
    end

Tableau to reason about Many-Valued Linear Temporal Logic with Future and Past.
"""
mutable struct MVLTLFPTableau <: ManyValuedMultiModalTableau
    const judgement::Bool
    const assertion::NTuple{2,Formula}
    const world::Point1D
    const frame::ManyValuedLinearOrder
    const father::Union{MVLTLFPTableau,Nothing}
    const children::Vector{MVLTLFPTableau}
    expanded::Bool
    closed::Bool

    function MVLTLFPTableau(
        judgement::Bool,
        assertion::NTuple{2,Formula},
        world::Point1D,
        frame::ManyValuedLinearOrder
    )
        return new(
            judgement,
            assertion,
            world,
            frame,
            nothing,
            Vector{MVLTLFPTableau}(),
            false,
            false
        )
    end

    function MVLTLFPTableau(
        judgement::Bool,
        assertion::NTuple{2,Formula},
        world::Point1D,
        frame::ManyValuedLinearOrder,
        father::MVLTLFPTableau
    )
        return new(
            judgement,
            assertion,
            world,
            frame,
            father,
            Vector{MVLTLFPTableau}(),
            false,
            false
        )
    end
end
