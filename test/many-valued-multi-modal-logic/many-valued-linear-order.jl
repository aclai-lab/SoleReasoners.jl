using SoleLogics.ManyValuedLogics: FiniteTruth, booleanalgebra, G3, H4, α, β
using SoleReasoners: ManyValuedLinearOrder
using StaticArrays: SMatrix

mvlt = SMatrix{1,1,FiniteTruth}([⊥])
mveq = SMatrix{1,1,FiniteTruth}([⊥])
@test_throws ErrorException(
    "(D,̃<,̃=) is not a many-valued linear order (1)"
) ManyValuedLinearOrder(mvlt, mveq, booleanalgebra)

mvlt = SMatrix{1,1,FiniteTruth}([⊤])
mveq = SMatrix{1,1,FiniteTruth}([⊤])
@test_throws ErrorException(
    "(D,̃<,̃=) is not a many-valued linear order (3)"
) ManyValuedLinearOrder(mvlt, mveq, booleanalgebra)

mvlt = SMatrix{2,2,FiniteTruth}([[⊥ ⊥]; [⊥ ⊥]])
mveq = SMatrix{2,2,FiniteTruth}([[⊤ ⊤]; [⊥ ⊤]])
@test_throws ErrorException(
    "(D,̃<,̃=) is not a many-valued linear order (1)"
) ManyValuedLinearOrder(mvlt, mveq, booleanalgebra)

mvlt = SMatrix{2,2,FiniteTruth}([[⊥ ⊥]; [⊥ ⊥]])
mveq = SMatrix{2,2,FiniteTruth}([[⊤ α]; [⊥ ⊤]])
@test_throws ErrorException(
    "(D,̃<,̃=) is not a many-valued linear order (2)"
) ManyValuedLinearOrder(mvlt, mveq, G3)

mvlt = SMatrix{2,2,FiniteTruth}([[⊥ ⊥]; [⊥ ⊥]])
mveq = SMatrix{2,2,FiniteTruth}([[⊤ ⊥]; [⊥ ⊤]])
@test_throws ErrorException(
    "(D,̃<,̃=) is not a many-valued linear order (6)"
) ManyValuedLinearOrder(mvlt, mveq, booleanalgebra)

mvlt = SMatrix{2,2,FiniteTruth}([[⊥ ⊤]; [⊥ ⊥]])
mveq = SMatrix{2,2,FiniteTruth}([[⊤ α]; [α ⊤]])
@test_throws ErrorException(
    "(D,̃<,̃=) is not a many-valued linear order (7)"
) ManyValuedLinearOrder(mvlt, mveq, booleanalgebra)

mvlt = SMatrix{3,3,FiniteTruth}([[⊥ ⊤ ⊥]; [⊥ ⊥ ⊤]; [⊥ ⊥ ⊥]])
mveq = SMatrix{3,3,FiniteTruth}([[⊤ ⊥ ⊥]; [⊥ ⊤ ⊥]; [⊥ ⊥ ⊤]])
@test_throws ErrorException(
    "(D,̃<,̃=) is not a many-valued linear order (4)"
) ManyValuedLinearOrder(mvlt, mveq, booleanalgebra)

mvlt = SMatrix{3,3,FiniteTruth}([[⊥ α ⊥]; [⊥ ⊥ β]; [⊥ ⊥ ⊥]])
mveq = SMatrix{3,3,FiniteTruth}([[⊤ ⊥ ⊥]; [⊥ ⊤ ⊥]; [⊥ ⊥ ⊤]])
@test_throws ErrorException(
    "(D,̃<,̃=) is not a many-valued linear order (5)"
) ManyValuedLinearOrder(mvlt, mveq, H4)

mvlt = SMatrix{1,1,FiniteTruth}([⊥])
mveq = SMatrix{1,1,FiniteTruth}([⊤])
@test_nowarn o = ManyValuedLinearOrder(mvlt, mveq, booleanalgebra)
