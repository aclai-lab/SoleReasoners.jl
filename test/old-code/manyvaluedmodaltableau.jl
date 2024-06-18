using SoleLogics
using SoleReasoners
using Test

using SoleLogics.ManyValuedLogics: FiniteHeytingAlgebra
using SoleLogics.ManyValuedLogics: G3
using SoleLogics.ManyValuedLogics: α
using SoleReasoners: manyvaluedmodalalphaprove

X, Y = Atom.(["X", "Y"])
@test manyvaluedmodalalphaprove(
    α,
    # ((α→◊X)∧(⊤→□Y))→◊(X∧Y)
    →(
        ∧(
            →(
                α,
                ◊(X),
            ),
            →(
                ⊤,
                □(Y)
            )
        ),
        ◊(
            ∧(
                X,
                Y
            )
        )
    ),
    FiniteHeytingAlgebra(G3),
    verbose=true
) == true
