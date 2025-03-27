"""
    mutable struct MVCLTableau <: ManyValuedMultiModalTableau
        const judgement::Bool
        const assertion::NTuple{2,Formula}
        const world::Point2D
        const frame::NTuple{2,ManyValuedLinearOrder}
        const father::Union{MVCLTableau,Nothing}
        const children::Vector{MVCLTableau}
        expanded::Bool
        closed::Bool
    end

Tableau to reason about Many-Valued Compass Logic.
"""
mutable struct MVCLTableau <: ManyValuedMultiModalTableau
    const judgement::Bool
    const assertion::NTuple{2,Formula}
    const world::Point2D
    const frame::NTuple{2,ManyValuedLinearOrder}
    const father::Union{MVCLTableau,Nothing}
    const children::Vector{MVCLTableau}
    expanded::Bool
    closed::Bool

    function MVCLTableau(
        judgement::Bool,
        assertion::NTuple{2,Formula},
        world::Point2D,
        frame::NTuple{2,ManyValuedLinearOrder}
    )
        return new(
            judgement,
            assertion,
            world,
            frame,
            nothing,
            Vector{MVCLTableau}(),
            false,
            false
        )
    end

    function MVCLTableau(
        judgement::Bool,
        assertion::NTuple{2,Formula},
        world::Point2D,
        frame::NTuple{2,ManyValuedLinearOrder},
        father::MVCLTableau
    )
        newtableau = new(
            judgement,
            assertion,
            world,
            frame,
            father,
            Vector{MVCLTableau}(),
            false,
            false
        )
        pushchild!(father, newtableau)
        return newtableau
    end
end
