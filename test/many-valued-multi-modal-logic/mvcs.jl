using SoleReasoners: Point2D

x = Point1D("x")
y = Point1D("y")
@test_nowarn p = Point2D(x, y)
p = Point2D(x, y)
b = IOBuffer()
print(b, p)
@test String(take!(b)) == "(x,y)"
