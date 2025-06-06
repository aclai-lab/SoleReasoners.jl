using SoleLogics.ManyValuedLogics: FiniteTruth, booleanalgebra, G3, H4, α, β
using SoleReasoners: ManyValuedLinearOrder
using SoleReasoners: isaManyValuedLinearOrder, cardinality
using StaticArrays: SMatrix

################################################################################
# Constructor ##################################################################
################################################################################
mvlttable = SMatrix{1,1,FiniteTruth}([⊥])
mveqtable = SMatrix{1,1,FiniteTruth}([⊥])
@test !isaManyValuedLinearOrder(mvlttable, mveqtable, booleanalgebra)
@test_throws ErrorException(
    "(D,̃<,̃=) is not a many-valued linear order (1)"
) ManyValuedLinearOrder(mvlttable, mveqtable, booleanalgebra)

mvlttable = SMatrix{1,1,FiniteTruth}([⊤])
mveqtable = SMatrix{1,1,FiniteTruth}([⊤])
@test !isaManyValuedLinearOrder(mvlttable, mveqtable, booleanalgebra)
@test_throws ErrorException(
    "(D,̃<,̃=) is not a many-valued linear order (3)"
) ManyValuedLinearOrder(mvlttable, mveqtable, booleanalgebra)

mvlttable = SMatrix{2,2,FiniteTruth}([[⊥ ⊥]; [⊥ ⊥]])
mveqtable = SMatrix{2,2,FiniteTruth}([[⊤ ⊤]; [⊥ ⊤]])
@test !isaManyValuedLinearOrder(mvlttable, mveqtable, booleanalgebra)
@test_throws ErrorException(
    "(D,̃<,̃=) is not a many-valued linear order (1)"
) ManyValuedLinearOrder(mvlttable, mveqtable, booleanalgebra)

mvlttable = SMatrix{2,2,FiniteTruth}([[⊥ ⊥]; [⊥ ⊥]])
mveqtable = SMatrix{2,2,FiniteTruth}([[⊤ α]; [⊥ ⊤]])
@test !isaManyValuedLinearOrder(mvlttable, mveqtable, G3)
@test_throws ErrorException(
    "(D,̃<,̃=) is not a many-valued linear order (2)"
) ManyValuedLinearOrder(mvlttable, mveqtable, G3)

mvlttable = SMatrix{2,2,FiniteTruth}([[⊥ ⊥]; [⊥ ⊥]])
mveqtable = SMatrix{2,2,FiniteTruth}([[⊤ ⊥]; [⊥ ⊤]])
@test !isaManyValuedLinearOrder(mvlttable, mveqtable, booleanalgebra)
@test_throws ErrorException(
    "(D,̃<,̃=) is not a many-valued linear order (6)"
) ManyValuedLinearOrder(mvlttable, mveqtable, booleanalgebra)

mvlttable = SMatrix{2,2,FiniteTruth}([[⊥ ⊤]; [⊥ ⊥]])
mveqtable = SMatrix{2,2,FiniteTruth}([[⊤ α]; [α ⊤]])
@test !isaManyValuedLinearOrder(mvlttable, mveqtable, booleanalgebra)
@test_throws ErrorException(
    "(D,̃<,̃=) is not a many-valued linear order (7)"
) ManyValuedLinearOrder(mvlttable, mveqtable, booleanalgebra)

mvlttable = SMatrix{3,3,FiniteTruth}([[⊥ ⊤ ⊥]; [⊥ ⊥ ⊤]; [⊥ ⊥ ⊥]])
mveqtable = SMatrix{3,3,FiniteTruth}([[⊤ ⊥ ⊥]; [⊥ ⊤ ⊥]; [⊥ ⊥ ⊤]])
@test !isaManyValuedLinearOrder(mvlttable, mveqtable, booleanalgebra)
@test_throws ErrorException(
    "(D,̃<,̃=) is not a many-valued linear order (4)"
) ManyValuedLinearOrder(mvlttable, mveqtable, booleanalgebra)

mvlttable = SMatrix{3,3,FiniteTruth}([[⊥ α ⊥]; [⊥ ⊥ β]; [⊥ ⊥ ⊥]])
mveqtable = SMatrix{3,3,FiniteTruth}([[⊤ ⊥ ⊥]; [⊥ ⊤ ⊥]; [⊥ ⊥ ⊤]])
@test !isaManyValuedLinearOrder(mvlttable, mveqtable, H4)
@test_throws ErrorException(
    "(D,̃<,̃=) is not a many-valued linear order (5)"
) ManyValuedLinearOrder(mvlttable, mveqtable, H4)

mvlttable = SMatrix{1,1,FiniteTruth}([⊥])
mveqtable = SMatrix{1,1,FiniteTruth}([⊤])
@test_nowarn isaManyValuedLinearOrder(mvlttable, mveqtable, booleanalgebra)
@test_nowarn o = ManyValuedLinearOrder(mvlttable, mveqtable, booleanalgebra)

################################################################################
# Logger #######################################################################
################################################################################
mvlttable = SMatrix{2,2,FiniteTruth}([[⊥ ⊤]; [⊥ ⊥]])
mveqtable = SMatrix{2,2,FiniteTruth}([[⊤ ⊥]; [⊥ ⊤]])
o = ManyValuedLinearOrder(mvlttable, mveqtable, booleanalgebra)
b = IOBuffer()
print(b, o)
@test String(take!(b)) == " ̃<: FiniteTruth[⊥ ⊤; ⊥ ⊥]\n ̃=: FiniteTruth[⊤ ⊥; ⊥ ⊤]"

################################################################################
# Utils ########################################################################
################################################################################
@test cardinality(o) == 2
