using SoleLogics: LTLFP_F, LTLFP_P
using SoleLogics.ManyValuedLogics: FiniteTruth, booleanalgebra
using SoleReasoners: ManyValuedLinearOrder, Point1D, mveval, mveq, mvlt
using StaticArrays: SMatrix

################################################################################
# Constructor ##################################################################
################################################################################
@test_throws ErrorException("0 is not a valid index in Julia") x1 = Point1D(0)
@test_nowarn x1 = Point1D(UInt8(1))
@test_nowarn x1 = Point1D(UInt(1))
@test_nowarn x1 = Point1D(1)

################################################################################
# Logger #######################################################################
################################################################################
x1 = Point1D(UInt8(1))
b = IOBuffer()
print(b, x1)
@test String(take!(b)) == "x1"

################################################################################
# Many-valued linear order functions ###########################################
################################################################################
x2 = Point1D(UInt8(2))
mvlttable = SMatrix{2,2,FiniteTruth}([[⊥ ⊤]; [⊥ ⊥]])
mveqtable = SMatrix{2,2,FiniteTruth}([[⊤ ⊥]; [⊥ ⊤]])
o = ManyValuedLinearOrder(mvlttable, mveqtable, booleanalgebra)
@test isbot(mvlt(x1, x1, o))
@test istop(mvlt(x1, x2, o))
@test isbot(mvlt(x2, x1, o))
@test isbot(mvlt(x2, x2, o))
@test istop(mveq(x1, x1, o))
@test isbot(mveq(x1, x2, o))
@test isbot(mveq(x2, x1, o))
@test istop(mveq(x2, x2, o))

################################################################################
# Many-valued evaluation functions (CRISP case) ################################
################################################################################
@test isbot(mveval(LTLFP_F, x1, x1, o))
@test istop(mveval(LTLFP_F, x1, x2, o))
@test isbot(mveval(LTLFP_F, x2, x1, o))
@test isbot(mveval(LTLFP_F, x2, x2, o))
@test isbot(mveval(LTLFP_P, x1, x1, o))
@test isbot(mveval(LTLFP_P, x1, x2, o))
@test istop(mveval(LTLFP_P, x2, x1, o))
@test isbot(mveval(LTLFP_P, x2, x2, o))
