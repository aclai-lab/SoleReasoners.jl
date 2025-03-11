using SoleReasoners: Rectangle

x1 = Point1D(1)
x2 = Point1D(2)
y1 = Point1D(1)
y2 = Point1D(2)
ix = Interval(x1, x2)
iy = Interval(y1, y2)
@test_nowarn Rectangle(ix, iy)
r = Rectangle(ix, iy)
b = IOBuffer()
print(b, r)
@test String(take!(b)) == "([x1,x2],[y1,y2])"
