using SoleReasoners: Interval

x = Point1D("x")
y = Point1D("y")
@test_nowarn i = Interval(x, y)
i = Interval(x, y)
b = IOBuffer()
print(b, i)
@test String(take!(b)) == "[x,y]"
