using SoleLogics: HS_A
using SoleLogics.ManyValuedLogics: FiniteTruth, booleanalgebra
using SoleReasoners: ManyValuedLinearOrder, Point1D, Interval, mveval
using StaticArrays: SMatrix

################################################################################
# Constructor ##################################################################
################################################################################
x1 = Point1D(1)
x2 = Point1D(2)
mvlttable = SMatrix{2,2,FiniteTruth}([[⊥ ⊤]; [⊥ ⊥]])
mveqtable = SMatrix{2,2,FiniteTruth}([[⊤ ⊥]; [⊥ ⊤]])
o = ManyValuedLinearOrder(mvlttable, mveqtable, booleanalgebra)
@test_throws ErrorException(
    "`p1` and `p2` do not form an `Interval` in `o`"
) Interval(x2, x1, o)
@test_nowarn i1 = Interval(x1, x2, o)

################################################################################
# Logger #######################################################################
################################################################################
i1 = Interval(x1, x2, o)
b = IOBuffer()
print(b, i1)
@test String(take!(b)) == "[x1,x2]"

################################################################################
# Many-valued evaluation functions (CRISP case) ################################
################################################################################
x3 = Point1D(3)
x4 = Point1D(4)
mvlttable = SMatrix{4,4,FiniteTruth}(
    [[⊥ ⊤ ⊤ ⊤]; [⊥ ⊥ ⊤ ⊤]; [⊥ ⊥ ⊥ ⊤]; [⊥ ⊥ ⊥ ⊥]]
)
mveqtable = SMatrix{4,4,FiniteTruth}(
    [[⊤ ⊥ ⊥ ⊥]; [⊥ ⊤ ⊥ ⊥]; [⊥ ⊥ ⊤ ⊥]; [⊥ ⊥ ⊥ ⊤]]
)
o = ManyValuedLinearOrder(mvlttable, mveqtable, booleanalgebra)
x1x2 = Interval(x1, x2, o)
x1x3 = Interval(x1, x3, o)
x1x4 = Interval(x1, x4, o)
x2x3 = Interval(x2, x3, o)
x2x4 = Interval(x2, x4, o)
x3x4 = Interval(x3, x4, o)

@test isbot(mveval(HS_A, x1x2, x1x2, o))
@test isbot(mveval(HS_A, x1x2, x1x3, o))
@test isbot(mveval(HS_A, x1x2, x1x4, o))
@test istop(mveval(HS_A, x1x2, x2x3, o))
@test istop(mveval(HS_A, x1x2, x2x4, o))
@test isbot(mveval(HS_A, x1x2, x3x4, o))
@test isbot(mveval(HS_A, x1x3, x1x2, o))
@test isbot(mveval(HS_A, x1x3, x1x3, o))
@test isbot(mveval(HS_A, x1x3, x1x4, o))
@test isbot(mveval(HS_A, x1x3, x2x3, o))
@test isbot(mveval(HS_A, x1x3, x2x4, o))
@test istop(mveval(HS_A, x1x3, x3x4, o))
@test isbot(mveval(HS_A, x1x4, x1x2, o))
@test isbot(mveval(HS_A, x1x4, x1x3, o))
@test isbot(mveval(HS_A, x1x4, x1x4, o))
@test isbot(mveval(HS_A, x1x4, x2x3, o))
@test isbot(mveval(HS_A, x1x4, x2x4, o))
@test isbot(mveval(HS_A, x1x4, x3x4, o))
@test isbot(mveval(HS_A, x2x3, x1x2, o))
@test isbot(mveval(HS_A, x2x3, x1x3, o))
@test isbot(mveval(HS_A, x2x3, x1x4, o))
@test isbot(mveval(HS_A, x2x3, x2x3, o))
@test isbot(mveval(HS_A, x2x3, x2x4, o))
@test istop(mveval(HS_A, x2x3, x3x4, o))
@test isbot(mveval(HS_A, x2x4, x1x2, o))
@test isbot(mveval(HS_A, x2x4, x1x3, o))
@test isbot(mveval(HS_A, x2x4, x1x4, o))
@test isbot(mveval(HS_A, x2x4, x2x3, o))
@test isbot(mveval(HS_A, x2x4, x2x4, o))
@test isbot(mveval(HS_A, x2x4, x3x4, o))
@test isbot(mveval(HS_A, x3x4, x1x2, o))
@test isbot(mveval(HS_A, x3x4, x1x3, o))
@test isbot(mveval(HS_A, x3x4, x1x4, o))
@test isbot(mveval(HS_A, x3x4, x2x3, o))
@test isbot(mveval(HS_A, x3x4, x2x4, o))
@test isbot(mveval(HS_A, x3x4, x3x4, o))
