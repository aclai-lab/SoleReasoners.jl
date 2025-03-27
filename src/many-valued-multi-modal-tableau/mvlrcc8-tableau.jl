"""
Tableau to reason about Many-Valued Lutz and Wolter's modal logic of topological
relations with rectangular areas aligned with the axes.
"""
mutable struct MVLRCC8Tableau <: ManyValuedMultiModalTableau
    const judgement::Bool
    const assertion::NTuple{2,Formula}
    const world::Rectangle
    const frame::NTuple{2,ManyValuedLinearOrder}
    const father::Union{MVLRCC8Tableau,Nothing}
    const children::Vector{MVLRCC8Tableau}
    expanded::Bool
    closed::Bool

    function MVLRCC8Tableau(
        judgement::Bool,
        assertion::NTuple{2,Formula},
        world::Rectangle,
        frame::NTuple{2,ManyValuedLinearOrder}
    )
        return new(
            judgement,
            assertion,
            world,
            frame,
            nothing,
            Vector{MVLRCC8Tableau}(),
            false,
            false
        )
    end

    function MVLRCC8Tableau(
        judgement::Bool,
        assertion::NTuple{2,Formula},
        world::Rectangle,
        frame::NTuple{2,ManyValuedLinearOrder},
        father::MVLRCC8Tableau
    )
        return new(
            judgement,
            assertion,
            world,
            frame,
            father,
            Vector{MVLRCC8Tableau}(),
            false,
            false
        )
    end
end
