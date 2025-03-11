using SoleReasoners: Point1D

@test_nowarn x = Point1D("x")
x = Point1D("x")
b = IOBuffer()
print(b, x)
@test String(take!(b)) == "x"
