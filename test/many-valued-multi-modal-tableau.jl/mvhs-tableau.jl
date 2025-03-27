using SoleLogics.ManyValuedLogics: FiniteTruth, booleanalgebra
using SoleReasoners: ManyValuedLinearOrder, Point1D, Interval
using SoleReasoners: MVHSTableau, judgement, assertion, world, frame, father
using SoleReasoners: children, expanded, closed, isroot, expand!, close!
using StaticArrays: SMatrix

################################################################################
# Constructor ##################################################################
################################################################################
p,q = Atom.(["p","q"])
φ = ∧(p, q)
x1 = Point1D(UInt8(1))
x2 = Point1D(UInt8(2))
mvlttable = SMatrix{2,2,FiniteTruth}([[⊥ ⊤]; [⊥ ⊥]])
mveqtable = SMatrix{2,2,FiniteTruth}([[⊤ ⊥]; [⊥ ⊤]])
o = ManyValuedLinearOrder(mvlttable, mveqtable, booleanalgebra)
i1 = Interval(x1, x2, o)
@test_nowarn t0 = MVHSTableau(true, (⊤, φ), i1, o)
t0 = MVHSTableau(true, (⊤, φ), i1, o)
@test_nowarn t1 = MVHSTableau(true, (⊤, p), i1, o, t0)
t1 = MVHSTableau(true, (⊤, p), i1, o, t0)
@test_nowarn t2 = MVHSTableau(true, (⊤, q), i1, o, t1)

################################################################################
# Logger #######################################################################
################################################################################
t0 = MVHSTableau(true, (⊤, φ), i1, o)
t1 = MVHSTableau(true, (⊤, p), i1, o, t0)
t2 = MVHSTableau(true, (⊤, q), i1, o, t1)
b = IOBuffer()
print(b, t0)
@test String(take!(b)) == "true(⊤ ⪯ p ∧ q, [x1,x2], F)"
print(b, t1)
@test String(take!(b)) == "true(⊤ ⪯ p, [x1,x2], F)"
print(b, t2)
@test String(take!(b)) == "true(⊤ ⪯ q, [x1,x2], F)"

################################################################################
# Core operations ##############################################################
################################################################################
@test judgement(t0) == true
@test assertion(t0) == (⊤, φ)
@test world(t0) == i1
@test frame(t0) == o
@test isnothing(father(t0))
@test children(t0) == [t1]
@test expanded(t0) == false
@test closed(t0) == false
@test isroot(t0) == true
expand!(t0)
@test expanded(t0) == true
close!(t0)
@test closed(t0) == true

@test judgement(t1) == true
@test assertion(t1) == (⊤, p)
@test world(t1) == i1
@test frame(t1) == o
@test father(t1) == t0
@test children(t1) == [t2]
@test expanded(t1) == false
@test closed(t1) == false
@test isroot(t1) == false
expand!(t1)
@test expanded(t1) == true
close!(t1)
@test closed(t1) == true

@test judgement(t2) == true
@test assertion(t2) == (⊤, q)
@test world(t2) == i1
@test frame(t2) == o
@test father(t2) == t1
@test isempty(children(t2))
@test expanded(t2) == false
@test closed(t2) == false
@test isroot(t2) == false
expand!(t2)
@test expanded(t2) == true
close!(t2)
@test closed(t2) == true
