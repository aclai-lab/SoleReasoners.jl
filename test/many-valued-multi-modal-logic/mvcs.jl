using SoleReasoners: Point2D

x1 = Point1D(UInt8(1))
y1 = Point1D(UInt8(1))
@test_nowarn p1 = Point2D(x1, y1)
p1 = Point2D(x1, y1)
b = IOBuffer()
print(b, p1)
@test String(take!(b)) == "(x1,y1)"
