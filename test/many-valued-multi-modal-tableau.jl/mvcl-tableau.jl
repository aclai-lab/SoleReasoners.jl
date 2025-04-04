using SoleLogics.ManyValuedLogics: FiniteTruth, booleanalgebra
using SoleReasoners: ManyValuedLinearOrder, Point1D, Point2D
using SoleReasoners: MVCLTableau, judgement, assertion, world, frame, father
using SoleReasoners: children, expanded, closed, isroot, isleaf, expand!, close!
using SoleReasoners: findexpansionnode
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
ox = ManyValuedLinearOrder(mvlttable, mveqtable, booleanalgebra)
y1 = Point1D(UInt8(1))
y2 = Point1D(UInt8(2))
oy = ManyValuedLinearOrder(mvlttable, mveqtable, booleanalgebra)
p1 = Point2D(x1, y1)
@test_nowarn t0 = MVCLTableau(true, (⊤, φ), p1, (ox, oy))
t0 = MVCLTableau(true, (⊤, φ), p1, (ox, oy))
@test_nowarn t1 = MVCLTableau(true, (⊤, p), p1, (ox, oy), t0)
t1 = MVCLTableau(true, (⊤, p), p1, (ox, oy), t0)
@test_nowarn t2 = MVCLTableau(true, (⊤, q), p1, (ox, oy), t1)

################################################################################
# Logger #######################################################################
################################################################################
t0 = MVCLTableau(true, (⊤, φ), p1, (ox, oy))
t1 = MVCLTableau(true, (⊤, p), p1, (ox, oy), t0)
t2 = MVCLTableau(true, (⊤, q), p1, (ox, oy), t1)
b = IOBuffer()
print(b, t0)
@test String(take!(b)) == "true(⊤ ⪯ p ∧ q, (x1,y1), F)"
print(b, t1)
@test String(take!(b)) == "true(⊤ ⪯ p, (x1,y1), F)"
print(b, t2)
@test String(take!(b)) == "true(⊤ ⪯ q, (x1,y1), F)"

################################################################################
# Core operations ##############################################################
################################################################################
@test judgement(t0) == true
@test assertion(t0) == (⊤, φ)
@test world(t0) == p1
@test frame(t0) == (ox, oy)
@test isnothing(father(t0))
@test children(t0) == [t1]
@test expanded(t0) == false
@test closed(t0) == false
@test isroot(t0) == true
@test isleaf(t0) == false

@test judgement(t1) == true
@test assertion(t1) == (⊤, p)
@test world(t1) == p1
@test frame(t1) == (ox, oy)
@test father(t1) == t0
@test children(t1) == [t2]
@test expanded(t1) == false
@test closed(t1) == false
@test isroot(t1) == false
@test isleaf(t1) == false

@test judgement(t2) == true
@test assertion(t2) == (⊤, q)
@test world(t2) == p1
@test frame(t2) == (ox, oy)
@test father(t2) == t1
@test isempty(children(t2))
@test expanded(t2) == false
@test closed(t2) == false
@test isroot(t2) == false
@test isleaf(t2) == true

@test findexpansionnode(t2) == t0
expand!(t0)
@test expanded(t0) == true
@test expanded(t1) == false
@test expanded(t2) == false
@test findexpansionnode(t2) == t1
expand!(t1)
@test expanded(t0) == true
@test expanded(t1) == true
@test expanded(t2) == false
@test findexpansionnode(t2) == t2

@test findleaves(t0) == [t2]
@test findleaves(t1) == [t2]
@test findleaves(t2) == [t2]

close!(t1)
@test closed(t0) == true
@test closed(t1) == true
@test closed(t2) == true

φ = ∨(p, q)
t0 = MVCLTableau(true, (⊤, φ), p1, (ox, oy))
t1 = MVCLTableau(true, (⊤, p), p1, (ox, oy), t0)
t2 = MVCLTableau(true, (⊤, q), p1, (ox, oy), t0)

@test isnothing(father(t0))
@test children(t0) == [t1, t2]
@test closed(t0) == false
@test isroot(t0) == true
@test isleaf(t0) == false

@test father(t1) == t0
@test isempty(children(t1))
@test closed(t1) == false
@test isroot(t1) == false
@test isleaf(t1) == true

@test father(t2) == t0
@test isempty(children(t2))
@test closed(t2) == false
@test isroot(t2) == false
@test isleaf(t2) == true

@test findexpansionnode(t1) == t0
@test findexpansionnode(t2) == t0
expand!(t0)
@test expanded(t0) == true
@test expanded(t1) == false
@test expanded(t2) == false
@test findexpansionnode(t1) == t1
@test findexpansionnode(t2) == t2

@test findleaves(t0) == [t1, t2]
@test findleaves(t1) == [t1]
@test findleaves(t2) == [t2]

close!(t1)
@test closed(t0) == false
@test closed(t1) == true
@test closed(t2) == false
close!(t2)
@test closed(t0) == true
@test closed(t1) == true
@test closed(t2) == true

ts = Vector{MVCLTableau}()
push!(ts, MVCLTableau(true, (⊤, φ), p1, (ox, oy)))
for i in 1:10000
    push!(ts, MVCLTableau(true, (⊤, φ), p1, (ox, oy), last(ts)))
end
l1 = MVCLTableau(true, (⊤, φ), p1, (ox, oy), last(ts))
l2 = MVCLTableau(true, (⊤, φ), p1, (ox, oy), last(ts))
l3 = MVCLTableau(true, (⊤, φ), p1, (ox, oy), last(ts))

@test findleaves(first(ts)) == [l1, l2, l3]

t0 = MVCLTableau(true, (⊤, φ), p1, (ox, oy))
t1 = MVCLTableau(true, (⊤, p), p1, (ox, oy), t0)
t2 = MVCLTableau(true, (⊤, q), p1, (ox, oy), t0)
t3 = MVCLTableau(true, (⊤, φ), p1, (ox, oy), t2)
t4 = MVCLTableau(true, (⊤, φ), p1, (ox, oy), t2)

@test findleaves(t0) == [t1, t3, t4]
