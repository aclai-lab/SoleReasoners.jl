using SoleLogics.ManyValuedLogics: FiniteTruth, booleanalgebra
using SoleReasoners: ManyValuedMultiModalTableau, ManyValuedLinearOrder
using SoleReasoners: worlds, newframes
using StaticArrays: SMatrix

################################################################################
# Constructor ##################################################################
################################################################################
mutable struct MyManyValuedMultiModalTableau <: ManyValuedMultiModalTableau
    const judgement::Nothing
    const assertion::NTuple{2, Nothing}
    const world::Nothing
    const frame::ManyValuedLinearOrder
    const father::Nothing
    const children::Nothing
    expanded::Nothing
    closed::Nothing

    function MyManyValuedMultiModalTableau(frame::ManyValuedLinearOrder)
        new(
            nothing,
            (nothing, nothing),
            nothing,
            frame,
            nothing,
            nothing,
            nothing,
            nothing
        )
    end
end

################################################################################
# Interface ####################################################################
################################################################################
o = ManyValuedLinearOrder(
    SMatrix{1,1,FiniteTruth}([⊥]),
    SMatrix{1,1,FiniteTruth}([⊤]),
    booleanalgebra
)

@test_throws ErrorException(
    "Please, specify how to return all worlds in " *
    "`frame(t::MyManyValuedMultiModalTableau)`"
) worlds(MyManyValuedMultiModalTableau, o)

myManyValuedMultiModalTableau = MyManyValuedMultiModalTableau(o)

@test_throws ErrorException(
    "Please, specify how to generate new frames for " *
    "`t::MyManyValuedMultiModalTableau`"
) newframes(myManyValuedMultiModalTableau, booleanalgebra)
