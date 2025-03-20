using SoleLogics: LRCC8_Rec_DC, LRCC8_Rec_EC, LRCC8_Rec_PO
using SoleLogics: LRCC8_Rec_TPP, LRCC8_Rec_TPPi, LRCC8_Rec_NTPP, LRCC8_Rec_NTPPi
using SoleLogics.ManyValuedLogics: FiniteTruth, booleanalgebra
using SoleReasoners: ManyValuedLinearOrder, Point1D, Interval, Rectangle
using SoleReasoners: isaInterval, mveval
using StaticArrays: SMatrix

################################################################################
# Constructor ##################################################################
################################################################################
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

################################################################################
# Logger #######################################################################
################################################################################
r = Rectangle(ix, iy)
b = IOBuffer()
print(b, r)
@test String(take!(b)) == "([x1,x2],[y1,y2])"

################################################################################
# Many-valued evaluation functions (CRISP case) ################################
################################################################################
mvlttable = SMatrix{10,10,FiniteTruth}([
    [⊥ ⊤ ⊤ ⊤ ⊤ ⊤ ⊤ ⊤ ⊤ ⊤];
    [⊥ ⊥ ⊤ ⊤ ⊤ ⊤ ⊤ ⊤ ⊤ ⊤];
    [⊥ ⊥ ⊥ ⊤ ⊤ ⊤ ⊤ ⊤ ⊤ ⊤];
    [⊥ ⊥ ⊥ ⊥ ⊤ ⊤ ⊤ ⊤ ⊤ ⊤];
    [⊥ ⊥ ⊥ ⊥ ⊥ ⊤ ⊤ ⊤ ⊤ ⊤];
    [⊥ ⊥ ⊥ ⊥ ⊥ ⊥ ⊤ ⊤ ⊤ ⊤];
    [⊥ ⊥ ⊥ ⊥ ⊥ ⊥ ⊥ ⊤ ⊤ ⊤];
    [⊥ ⊥ ⊥ ⊥ ⊥ ⊥ ⊥ ⊥ ⊤ ⊤];
    [⊥ ⊥ ⊥ ⊥ ⊥ ⊥ ⊥ ⊥ ⊥ ⊤];
    [⊥ ⊥ ⊥ ⊥ ⊥ ⊥ ⊥ ⊥ ⊥ ⊥];
])
mveqtable = SMatrix{10,10,FiniteTruth}([
    [⊤ ⊥ ⊥ ⊥ ⊥ ⊥ ⊥ ⊥ ⊥ ⊥];
    [⊥ ⊤ ⊥ ⊥ ⊥ ⊥ ⊥ ⊥ ⊥ ⊥];
    [⊥ ⊥ ⊤ ⊥ ⊥ ⊥ ⊥ ⊥ ⊥ ⊥];
    [⊥ ⊥ ⊥ ⊤ ⊥ ⊥ ⊥ ⊥ ⊥ ⊥];
    [⊥ ⊥ ⊥ ⊥ ⊤ ⊥ ⊥ ⊥ ⊥ ⊥];
    [⊥ ⊥ ⊥ ⊥ ⊥ ⊤ ⊥ ⊥ ⊥ ⊥];
    [⊥ ⊥ ⊥ ⊥ ⊥ ⊥ ⊤ ⊥ ⊥ ⊥];
    [⊥ ⊥ ⊥ ⊥ ⊥ ⊥ ⊥ ⊤ ⊥ ⊥];
    [⊥ ⊥ ⊥ ⊥ ⊥ ⊥ ⊥ ⊥ ⊤ ⊥];
    [⊥ ⊥ ⊥ ⊥ ⊥ ⊥ ⊥ ⊥ ⊥ ⊤];
])
ox = ManyValuedLinearOrder(mvlttable, mveqtable, booleanalgebra)
oy = ManyValuedLinearOrder(mvlttable, mveqtable, booleanalgebra)

inboundsInterval(p1, p2, o) = @inbounds Interval(p1, p2, o)

# r1 = [(x1, x2),(y1, y2)], r2 = [(z1, z2), (t1, t2)]
for x1 = 1:10, x2 = 1:10
    !isaInterval(x1, x2, ox) && continue
    local x1x2 = inboundsInterval(x1, x2, ox)
    for y1 = 1:10, y2 = 1:10
        !isaInterval(y1, y2, oy) && continue
        y1y2 = inboundsInterval(y1, y2, oy)
        for z1 = 1:10, z2 = 1:10
            !isaInterval(z1, z2, ox) && continue
            z1z2 = inboundsInterval(z1, z2, ox)
            for t1 = 1:10, t2 = 1:10
                !isaInterval(t1, t2, oy) && continue
                t1t2 = inboundsInterval(t1, t2, oy)
                r1 = Rectangle(x1x2, y1y2)
                r2 = Rectangle(z1z2, t1t2)
                if x2 < z1 || y2 < t1 || z2 < x1 || t2 < y1
                    @test istop(mveval(LRCC8_Rec_DC, r1, r2, (ox, oy)))
                    @test isbot(mveval(LRCC8_Rec_EC, r1, r2, (ox, oy)))
                    # @test isbot(mveval(LRCC8_Rec_PO, r1, r2, (ox, oy)))
                    @test isbot(mveval(LRCC8_Rec_TPP, r1, r2, (ox, oy)))
                    @test isbot(mveval(LRCC8_Rec_TPPi, r1, r2, (ox, oy)))
                    @test isbot(mveval(LRCC8_Rec_NTPP, r1, r2, (ox, oy)))
                    @test isbot(mveval(LRCC8_Rec_NTPPi, r1, r2, (ox, oy)))
                elseif x1 == z2 || x2 == z1 || y1 == t2 || y2 == t1
                    @test isbot(mveval(LRCC8_Rec_DC, r1, r2, (ox, oy)))
                    @test istop(mveval(LRCC8_Rec_EC, r1, r2, (ox, oy)))
                    # @test isbot(mveval(LRCC8_Rec_PO, r1, r2, (ox, oy)))
                    @test isbot(mveval(LRCC8_Rec_TPP, r1, r2, (ox, oy)))
                    @test isbot(mveval(LRCC8_Rec_TPPi, r1, r2, (ox, oy)))
                    @test isbot(mveval(LRCC8_Rec_NTPP, r1, r2, (ox, oy)))
                    @test isbot(mveval(LRCC8_Rec_NTPPi, r1, r2, (ox, oy)))
                elseif x1 < z1 < x2 < z2 || z1 < x1 < z2 < x2 ||
                       y1 < t1 < y2 < t2 || t1 < y1 < t2 < y1
                    @test isbot(mveval(LRCC8_Rec_DC, r1, r2, (ox, oy)))
                    @test isbot(mveval(LRCC8_Rec_EC, r1, r2, (ox, oy)))
                    # @test istop(mveval(LRCC8_Rec_PO, r1, r2, (ox, oy)))
                    @test isbot(mveval(LRCC8_Rec_TPP, r1, r2, (ox, oy)))
                    @test isbot(mveval(LRCC8_Rec_TPPi, r1, r2, (ox, oy)))
                    @test isbot(mveval(LRCC8_Rec_NTPP, r1, r2, (ox, oy)))
                    @test isbot(mveval(LRCC8_Rec_NTPPi, r1, r2, (ox, oy)))
                elseif (
                    x1 == z1 && z2 <= x2 && y1 <= t1 && t2 <= y2 ||
                    x2 == z2 && x1 <= z1 && y1 <= t1 && t2 <= y2 ||
                    y1 == t1 && x1 <= z1 && z2 <= x2 && t2 <= y2 ||
                    y2 == t2 && x1 <= z1 && z2 <= x2 && y1 <= t1
                ) && !(x1 == z1 && x2 == z2 && y1 == t1 && y2 == t2)
                    @test isbot(mveval(LRCC8_Rec_DC, r1, r2, (ox, oy)))
                    @test isbot(mveval(LRCC8_Rec_EC, r1, r2, (ox, oy)))
                    # @test isbot(mveval(LRCC8_Rec_PO, r1, r2, (ox, oy)))
                    @test istop(mveval(LRCC8_Rec_TPP, r1, r2, (ox, oy)))
                    @test isbot(mveval(LRCC8_Rec_TPPi, r1, r2, (ox, oy)))
                    @test isbot(mveval(LRCC8_Rec_NTPP, r1, r2, (ox, oy)))
                    @test isbot(mveval(LRCC8_Rec_NTPPi, r1, r2, (ox, oy)))   
                elseif (
                    x1 == z1 && x2 <= z2 && t1 <= y1 && y2 <= t2 ||
                    x2 == z2 && z1 <= x1 && t1 <= y1 && y2 <= t2 ||
                    y1 == t1 && z1 <= x1 && x2 <= z2 && y2 <= t2 ||
                    y2 == t2 && z1 <= x1 && x2 <= z2 && t1 <= y1
                ) && !(x1 == z1 && x2 == z2 && y1 == t1 && y2 == t2)
                    @test isbot(mveval(LRCC8_Rec_DC, r1, r2, (ox, oy)))
                    @test isbot(mveval(LRCC8_Rec_EC, r1, r2, (ox, oy)))
                    # @test isbot(mveval(LRCC8_Rec_PO, r1, r2, (ox, oy)))
                    @test isbot(mveval(LRCC8_Rec_TPP, r1, r2, (ox, oy)))
                    @test istop(mveval(LRCC8_Rec_TPPi, r1, r2, (ox, oy)))
                    @test isbot(mveval(LRCC8_Rec_NTPP, r1, r2, (ox, oy)))
                    @test isbot(mveval(LRCC8_Rec_NTPPi, r1, r2, (ox, oy)))               
                elseif x1 < z1 < z2 < x2 && y1 < t1 < t2 < y2
                    @test isbot(mveval(LRCC8_Rec_DC, r1, r2, (ox, oy)))
                    @test isbot(mveval(LRCC8_Rec_EC, r1, r2, (ox, oy)))
                    # @test isbot(mveval(LRCC8_Rec_PO, r1, r2, (ox, oy)))
                    @test isbot(mveval(LRCC8_Rec_TPP, r1, r2, (ox, oy)))
                    @test isbot(mveval(LRCC8_Rec_TPPi, r1, r2, (ox, oy)))
                    @test istop(mveval(LRCC8_Rec_NTPP, r1, r2, (ox, oy)))
                    @test isbot(mveval(LRCC8_Rec_NTPPi, r1, r2, (ox, oy)))
                elseif z1 < x1 < x2 < z2 && t1 < y1 < y2 < t2
                    @test isbot(mveval(LRCC8_Rec_DC, r1, r2, (ox, oy)))
                    @test isbot(mveval(LRCC8_Rec_EC, r1, r2, (ox, oy)))
                    # @test isbot(mveval(LRCC8_Rec_PO, r1, r2, (ox, oy)))
                    @test isbot(mveval(LRCC8_Rec_TPP, r1, r2, (ox, oy)))
                    @test isbot(mveval(LRCC8_Rec_TPPi, r1, r2, (ox, oy)))
                    @test isbot(mveval(LRCC8_Rec_NTPP, r1, r2, (ox, oy)))
                    @test istop(mveval(LRCC8_Rec_NTPPi, r1, r2, (ox, oy)))
                else
                    @test isbot(mveval(LRCC8_Rec_DC, r1, r2, (ox, oy)))
                    @test isbot(mveval(LRCC8_Rec_EC, r1, r2, (ox, oy)))
                    # @test isbot(mveval(LRCC8_Rec_PO, r1, r2, (ox, oy)))
                    @test isbot(mveval(LRCC8_Rec_TPP, r1, r2, (ox, oy)))
                    @test isbot(mveval(LRCC8_Rec_TPPi, r1, r2, (ox, oy)))
                    @test isbot(mveval(LRCC8_Rec_NTPP, r1, r2, (ox, oy)))
                    @test isbot(mveval(LRCC8_Rec_NTPPi, r1, r2, (ox, oy)))
                end                
            end
        end
    end
end
