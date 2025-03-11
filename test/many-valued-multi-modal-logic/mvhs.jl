using SoleReasoners: Interval

x1 = Point1D(1)
x2 = Point1D(2)
@test_nowarn i = Interval(x1, x2)
i = Interval(x1, x2)
b = IOBuffer()
print(b, i)
@test String(take!(b)) == "[x1,x2]"
