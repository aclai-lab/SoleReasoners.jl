using SoleReasoners: Rectangle

x1 = Point1D(1)
x2 = Point1D(2)
y1 = Point1D(1)
y2 = Point1D(2)
mvlttable = SMatrix{2,2,FiniteTruth}([[⊥ ⊤]; [⊥ ⊥]])
mveqtable = SMatrix{2,2,FiniteTruth}([[⊤ ⊥]; [⊥ ⊤]])
ox = ManyValuedLinearOrder(mvlttable, mveqtable, booleanalgebra)
oy = ManyValuedLinearOrder(mvlttable, mveqtable, booleanalgebra)
ix = Interval(x1, x2, ox)
iy = Interval(y1, y2, oy)
@test_nowarn Rectangle(ix, iy)
r = Rectangle(ix, iy)
b = IOBuffer()
print(b, r)
@test String(take!(b)) == "([x1,x2],[y1,y2])"
