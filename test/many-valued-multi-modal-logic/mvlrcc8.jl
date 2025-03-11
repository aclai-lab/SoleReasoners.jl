using SoleReasoners: Rectangle

x = Point1D("x")
y = Point1D("y")
z = Point1D("z")
t = Point1D("t")
xy = Interval(x, y)
zt = Interval(z, t)
@test_nowarn Rectangle(xy, zt)
r = Rectangle(xy, zt)
b = IOBuffer()
print(b, r)
@test String(take!(b)) == "([x,y],[z,t])"
