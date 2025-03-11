using SoleReasoners: Point1D

@test_throws ErrorException("0 is not a valid index in Julia") x1 = Point1D(0)
@test_nowarn x1 = Point1D(UInt8(1))
@test_nowarn x1 = Point1D(UInt(1))
@test_nowarn x1 = Point1D(1)
x1 = Point1D(UInt8(1))
b = IOBuffer()
print(b, x1)
@test String(take!(b)) == "x1"
