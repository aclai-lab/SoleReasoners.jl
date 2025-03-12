using SoleLogics: CL_N, CL_S, CL_E, CL_W
using SoleLogics.ManyValuedLogics: FiniteTruth, booleanalgebra
using SoleReasoners: ManyValuedLinearOrder, Point1D, Point2D, mveval
using StaticArrays: SMatrix

################################################################################
# Constructor ##################################################################
################################################################################
x1 = Point1D(UInt8(1))
y1 = Point1D(UInt8(1))
@test_nowarn p1 = Point2D(x1, y1)

################################################################################
# Logger #######################################################################
################################################################################
p1 = Point2D(x1, y1)
b = IOBuffer()
print(b, p1)
@test String(take!(b)) == "(x1,y1)"

################################################################################
# Many-valued evaluation functions (CRISP case) ################################
################################################################################
x2 = Point1D(UInt8(2))
y2 = Point1D(UInt8(2))
p2 = Point2D(x2,y1)
p3 = Point2D(x1,y2)
p4 = Point2D(x2, y2)
mvlttable = SMatrix{2,2,FiniteTruth}([[⊥ ⊤]; [⊥ ⊥]])
mveqtable = SMatrix{2,2,FiniteTruth}([[⊤ ⊥]; [⊥ ⊤]])
ox = ManyValuedLinearOrder(mvlttable, mveqtable, booleanalgebra)
oy = ManyValuedLinearOrder(mvlttable, mveqtable, booleanalgebra)

@test isbot(mveval(CL_N, p1, p1, (ox, oy)))
@test isbot(mveval(CL_N, p1, p2, (ox, oy)))
@test istop(mveval(CL_N, p1, p3, (ox, oy)))
@test isbot(mveval(CL_N, p1, p4, (ox, oy)))
@test isbot(mveval(CL_N, p2, p1, (ox, oy)))
@test isbot(mveval(CL_N, p2, p2, (ox, oy)))
@test isbot(mveval(CL_N, p2, p3, (ox, oy)))
@test istop(mveval(CL_N, p2, p4, (ox, oy)))
@test isbot(mveval(CL_N, p3, p1, (ox, oy)))
@test isbot(mveval(CL_N, p3, p2, (ox, oy)))
@test isbot(mveval(CL_N, p3, p3, (ox, oy)))
@test isbot(mveval(CL_N, p3, p4, (ox, oy)))
@test isbot(mveval(CL_N, p4, p1, (ox, oy)))
@test isbot(mveval(CL_N, p4, p2, (ox, oy)))
@test isbot(mveval(CL_N, p4, p3, (ox, oy)))
@test isbot(mveval(CL_N, p4, p4, (ox, oy)))

@test isbot(mveval(CL_S, p1, p1, (ox, oy)))
@test isbot(mveval(CL_S, p1, p2, (ox, oy)))
@test isbot(mveval(CL_S, p1, p3, (ox, oy)))
@test isbot(mveval(CL_S, p1, p4, (ox, oy)))
@test isbot(mveval(CL_S, p2, p1, (ox, oy)))
@test isbot(mveval(CL_S, p2, p2, (ox, oy)))
@test isbot(mveval(CL_S, p2, p3, (ox, oy)))
@test isbot(mveval(CL_S, p2, p4, (ox, oy)))
@test istop(mveval(CL_S, p3, p1, (ox, oy)))
@test isbot(mveval(CL_S, p3, p2, (ox, oy)))
@test isbot(mveval(CL_S, p3, p3, (ox, oy)))
@test isbot(mveval(CL_S, p3, p4, (ox, oy)))
@test isbot(mveval(CL_S, p4, p1, (ox, oy)))
@test istop(mveval(CL_S, p4, p2, (ox, oy)))
@test isbot(mveval(CL_S, p4, p3, (ox, oy)))
@test isbot(mveval(CL_S, p4, p4, (ox, oy)))

@test isbot(mveval(CL_E, p1, p1, (ox, oy)))
@test istop(mveval(CL_E, p1, p2, (ox, oy)))
@test isbot(mveval(CL_E, p1, p3, (ox, oy)))
@test isbot(mveval(CL_E, p1, p4, (ox, oy)))
@test isbot(mveval(CL_E, p2, p1, (ox, oy)))
@test isbot(mveval(CL_E, p2, p2, (ox, oy)))
@test isbot(mveval(CL_E, p2, p3, (ox, oy)))
@test isbot(mveval(CL_E, p2, p4, (ox, oy)))
@test isbot(mveval(CL_E, p3, p1, (ox, oy)))
@test isbot(mveval(CL_E, p3, p2, (ox, oy)))
@test isbot(mveval(CL_E, p3, p3, (ox, oy)))
@test istop(mveval(CL_E, p3, p4, (ox, oy)))
@test isbot(mveval(CL_E, p4, p1, (ox, oy)))
@test isbot(mveval(CL_E, p4, p2, (ox, oy)))
@test isbot(mveval(CL_E, p4, p3, (ox, oy)))
@test isbot(mveval(CL_E, p4, p4, (ox, oy)))

@test isbot(mveval(CL_W, p1, p1, (ox, oy)))
@test isbot(mveval(CL_W, p1, p2, (ox, oy)))
@test isbot(mveval(CL_W, p1, p3, (ox, oy)))
@test isbot(mveval(CL_W, p1, p4, (ox, oy)))
@test istop(mveval(CL_W, p2, p1, (ox, oy)))
@test isbot(mveval(CL_W, p2, p2, (ox, oy)))
@test isbot(mveval(CL_W, p2, p3, (ox, oy)))
@test isbot(mveval(CL_W, p2, p4, (ox, oy)))
@test isbot(mveval(CL_W, p3, p1, (ox, oy)))
@test isbot(mveval(CL_W, p3, p2, (ox, oy)))
@test isbot(mveval(CL_W, p3, p3, (ox, oy)))
@test isbot(mveval(CL_W, p3, p4, (ox, oy)))
@test isbot(mveval(CL_W, p4, p1, (ox, oy)))
@test isbot(mveval(CL_W, p4, p2, (ox, oy)))
@test istop(mveval(CL_W, p4, p3, (ox, oy)))
@test isbot(mveval(CL_W, p4, p4, (ox, oy)))
