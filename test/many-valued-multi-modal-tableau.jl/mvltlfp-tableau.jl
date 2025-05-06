using SoleLogics.ManyValuedLogics: FiniteTruth, booleanalgebra
using SoleLogics: LTLFP_F, LTLFP_P, box
using SoleReasoners: ManyValuedLinearOrder, Point1D
using SoleReasoners: MVLTLFPTableau, judgement, assertion, world, frame, father
using SoleReasoners: children, expanded, closed, isroot, isleaf, expand!, close!
using SoleReasoners: findexpansionnode, findleaves
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
@test_nowarn t0 = MVLTLFPTableau(true, (⊤, φ), x1, o)
t0 = MVLTLFPTableau(true, (⊤, φ), x1, o)
@test_nowarn t1 = MVLTLFPTableau(true, (⊤, p), x1, o, t0)
t1 = MVLTLFPTableau(true, (⊤, p), x1, o, t0)
@test_nowarn t2 = MVLTLFPTableau(true, (⊤, q), x1, o, t1)

################################################################################
# Logger #######################################################################
################################################################################
t0 = MVLTLFPTableau(true, (⊤, φ), x1, o)
t1 = MVLTLFPTableau(true, (⊤, p), x1, o, t0)
t2 = MVLTLFPTableau(true, (⊤, q), x1, o, t1)
b = IOBuffer()
print(b, t0)
@test String(take!(b)) == "true(⊤ ⪯ p ∧ q, x1, F)"
print(b, t1)
@test String(take!(b)) == "true(⊤ ⪯ p, x1, F)"
print(b, t2)
@test String(take!(b)) == "true(⊤ ⪯ q, x1, F)"

################################################################################
# Core operations ##############################################################
################################################################################
@test judgement(t0) == true
@test assertion(t0) == (⊤, φ)
@test world(t0) == x1
@test frame(t0) == o
@test isnothing(father(t0))
@test children(t0) == [t1]
@test expanded(t0) == false
@test closed(t0) == false
@test isroot(t0) == true
@test isleaf(t0) == false

@test judgement(t1) == true
@test assertion(t1) == (⊤, p)
@test world(t1) == x1
@test frame(t1) == o
@test father(t1) == t0
@test children(t1) == [t2]
@test expanded(t1) == false
@test closed(t1) == false
@test isroot(t1) == false
@test isleaf(t1) == false

@test judgement(t2) == true
@test assertion(t2) == (⊤, q)
@test world(t2) == x1
@test frame(t2) == o
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
t0 = MVLTLFPTableau(true, (⊤, φ), x1, o)
t1 = MVLTLFPTableau(true, (⊤, p), x1, o, t0)
t2 = MVLTLFPTableau(true, (⊤, q), x1, o, t0)

@test isnothing(father(t0))
@test children(t0) == [t1, t2]
@test expanded(t0) == false
@test closed(t0) == false
@test isroot(t0) == true
@test isleaf(t0) == false

@test father(t1) == t0
@test isempty(children(t1))
@test expanded(t1) == false
@test closed(t1) == false
@test isroot(t1) == false
@test isleaf(t1) == true

@test father(t2) == t0
@test isempty(children(t2))
@test expanded(t2) == false
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

ts = Vector{MVLTLFPTableau}()
push!(ts, MVLTLFPTableau(true, (⊤, φ), x1, o))
for i in 1:10000
    push!(ts, MVLTLFPTableau(true, (⊤, φ), x1, o, last(ts)))
end
l1 = MVLTLFPTableau(true, (⊤, φ), x1, o, last(ts))
l2 = MVLTLFPTableau(true, (⊤, φ), x1, o, last(ts))
l3 = MVLTLFPTableau(true, (⊤, φ), x1, o, last(ts))

@test findleaves(first(ts)) == [l1, l2, l3]

t0 = MVLTLFPTableau(true, (⊤, φ), x1, o)
t1 = MVLTLFPTableau(true, (⊤, p), x1, o, t0)
t2 = MVLTLFPTableau(true, (⊤, q), x1, o, t0)
t3 = MVLTLFPTableau(true, (⊤, φ), x1, o, t2)
t4 = MVLTLFPTableau(true, (⊤, φ), x1, o, t2)

@test findleaves(t0) == [t1, t3, t4]

################################################################################
# α-sat ########################################################################
################################################################################
using SoleLogics.ManyValuedLogics: G3, α
using SoleReasoners: MetricHeap, distancefromroot, inversedistancefromroot
using SoleReasoners: alphasat, roundrobin!

metricheaps = [
    MetricHeap(distancefromroot),
    MetricHeap(inversedistancefromroot),
    MetricHeap(distancefromroot)
]
t0 = MVLTLFPTableau(true, (⊤, ⊥), x1, o)
push!(metricheaps, t0)
@test !alphasat(metricheaps, roundrobin!, booleanalgebra)   # X1

metricheaps = [
    MetricHeap(distancefromroot),
    MetricHeap(inversedistancefromroot),
    MetricHeap(distancefromroot)
]
t0 = MVLTLFPTableau(false, (α, α), x1, o)
push!(metricheaps, t0)
@test !alphasat(metricheaps, roundrobin!, G3)   # X2

metricheaps = [
    MetricHeap(distancefromroot),
    MetricHeap(inversedistancefromroot),
    MetricHeap(distancefromroot)
]
t0 = MVLTLFPTableau(false, (⊥, α), x1, o)
push!(metricheaps, t0)
@test !alphasat(metricheaps, roundrobin!, G3)   # X3

metricheaps = [
    MetricHeap(distancefromroot),
    MetricHeap(inversedistancefromroot),
    MetricHeap(distancefromroot)
]
t0 = MVLTLFPTableau(false, (α, ⊤), x1, o)
push!(metricheaps, t0)
@test !alphasat(metricheaps, roundrobin!, G3)   # X4

metricheaps = [
    MetricHeap(distancefromroot),
    MetricHeap(inversedistancefromroot),
    MetricHeap(distancefromroot)
]
t0 = MVLTLFPTableau(false, (⊥, φ), x1, o)
push!(metricheaps, t0)
@test !alphasat(metricheaps, roundrobin!, booleanalgebra)   # X3

metricheaps = [
    MetricHeap(distancefromroot),
    MetricHeap(inversedistancefromroot),
    MetricHeap(distancefromroot)
]
t0 = MVLTLFPTableau(false, (φ, ⊤), x1, o)
push!(metricheaps, t0)
@test !alphasat(metricheaps, roundrobin!, booleanalgebra)   # X4

metricheaps = [
    MetricHeap(distancefromroot),
    MetricHeap(inversedistancefromroot),
    MetricHeap(distancefromroot)
]
t0 = MVLTLFPTableau(true, (⊤, φ), x1, o)
push!(metricheaps, t0)
t1 = MVLTLFPTableau(false, (α, φ), x1, o, t0)
push!(metricheaps, t1)
@test !alphasat(metricheaps, roundrobin!, G3)   # X5

metricheaps = [
    MetricHeap(distancefromroot),
    MetricHeap(inversedistancefromroot),
    MetricHeap(distancefromroot)
]
t0 = MVLTLFPTableau(false, (α, φ), x1, o)
push!(metricheaps, t0)
t1 = MVLTLFPTableau(true, (⊤, φ), x1, o, t0)
push!(metricheaps, t1)
@test !alphasat(metricheaps, roundrobin!, G3)   # X5

metricheaps = [
    MetricHeap(distancefromroot),
    MetricHeap(inversedistancefromroot),
    MetricHeap(distancefromroot)
]
t0 = MVLTLFPTableau(true, (⊤, ∧(⊥, ⊥)), x1, o)
push!(metricheaps, t0)
@test !alphasat(metricheaps, roundrobin!, booleanalgebra)    # T∧

metricheaps = [
    MetricHeap(distancefromroot),
    MetricHeap(inversedistancefromroot),
    MetricHeap(distancefromroot)
]
t0 = MVLTLFPTableau(true, (⊤, ∧(⊥, ⊤)), x1, o)
push!(metricheaps, t0)
@test !alphasat(metricheaps, roundrobin!, booleanalgebra)    # T∧

metricheaps = [
    MetricHeap(distancefromroot),
    MetricHeap(inversedistancefromroot),
    MetricHeap(distancefromroot)
]
t0 = MVLTLFPTableau(true, (⊤, ∧(⊤, ⊥)), x1, o)
push!(metricheaps, t0)
@test !alphasat(metricheaps, roundrobin!, booleanalgebra)    # T∧

metricheaps = [
    MetricHeap(distancefromroot),
    MetricHeap(inversedistancefromroot),
    MetricHeap(distancefromroot)
]
t0 = MVLTLFPTableau(true, (⊤, ∧(⊤, ⊤)), x1, o)
push!(metricheaps, t0)
@test alphasat(metricheaps, roundrobin!, booleanalgebra)    # T∧

metricheaps = [
    MetricHeap(distancefromroot),
    MetricHeap(inversedistancefromroot),
    MetricHeap(distancefromroot)
]
t0 = MVLTLFPTableau(true, (⊤, ∨(⊥, ⊥)), x1, o)
push!(metricheaps, t0)
@test !alphasat(metricheaps, roundrobin!, booleanalgebra)    # F∨

metricheaps = [
    MetricHeap(distancefromroot),
    MetricHeap(inversedistancefromroot),
    MetricHeap(distancefromroot)
]
t0 = MVLTLFPTableau(true, (⊤, ∨(⊥, ⊤)), x1, o)
push!(metricheaps, t0)
@test alphasat(metricheaps, roundrobin!, booleanalgebra)    # F∨

metricheaps = [
    MetricHeap(distancefromroot),
    MetricHeap(inversedistancefromroot),
    MetricHeap(distancefromroot)
]
t0 = MVLTLFPTableau(true, (⊤, ∨(⊤, ⊥)), x1, o)
push!(metricheaps, t0)
@test alphasat(metricheaps, roundrobin!, booleanalgebra)    # F∨

metricheaps = [
    MetricHeap(distancefromroot),
    MetricHeap(inversedistancefromroot),
    MetricHeap(distancefromroot)
]
t0 = MVLTLFPTableau(true, (⊤, ∨(⊤, ⊤)), x1, o)
push!(metricheaps, t0)
@test alphasat(metricheaps, roundrobin!, booleanalgebra)    # F∨

metricheaps = [
    MetricHeap(distancefromroot),
    MetricHeap(inversedistancefromroot),
    MetricHeap(distancefromroot)
]
t0 = MVLTLFPTableau(true, (⊤, →(⊥, ⊥)), x1, o)
push!(metricheaps, t0)
@test alphasat(metricheaps, roundrobin!, booleanalgebra)    # T→

metricheaps = [
    MetricHeap(distancefromroot),
    MetricHeap(inversedistancefromroot),
    MetricHeap(distancefromroot)
]
t0 = MVLTLFPTableau(true, (⊤, →(⊥, ⊤)), x1, o)
push!(metricheaps, t0)
@test alphasat(metricheaps, roundrobin!, booleanalgebra)    # T→

metricheaps = [
    MetricHeap(distancefromroot),
    MetricHeap(inversedistancefromroot),
    MetricHeap(distancefromroot)
]
t0 = MVLTLFPTableau(true, (⊤, →(⊤, ⊥)), x1, o)
push!(metricheaps, t0)
@test !alphasat(metricheaps, roundrobin!, booleanalgebra)    # T→

metricheaps = [
    MetricHeap(distancefromroot),
    MetricHeap(inversedistancefromroot),
    MetricHeap(distancefromroot)
]
t0 = MVLTLFPTableau(true, (⊤, →(⊤, ⊤)), x1, o)
push!(metricheaps, t0)
@test alphasat(metricheaps, roundrobin!, booleanalgebra)    # T→

metricheaps = [
    MetricHeap(distancefromroot),
    MetricHeap(inversedistancefromroot),
    MetricHeap(distancefromroot)
]
t0 = MVLTLFPTableau(true, (⊤, φ), x1, o)
push!(metricheaps, t0)
@test alphasat(metricheaps, roundrobin!, booleanalgebra)
