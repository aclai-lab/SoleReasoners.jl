using Random: rand, Xoshiro
using SoleReasoners: AbstractTableau, MetricHeap
using SoleReasoners: heap, metricvalue, tableau, roundrobin!, mostvoted!
using SoleReasoners: randombranch, distancefromroot, inversedistancefromroot
using SoleReasoners: father, children, expand!, close!, pushchild!

################################################################################
# Constructor ##################################################################
################################################################################
mutable struct LabeledTableau <: AbstractTableau
    const label::String
    const father::Union{LabeledTableau, Nothing}
    const children::Vector{LabeledTableau}
    expanded::Bool
    closed::Bool

    function LabeledTableau(label::String)
        return new(label, nothing, Vector{LabeledTableau}(), false, false)
    end

    function LabeledTableau(label::String, father::LabeledTableau)
        newtableau = new(label, father, Vector{LabeledTableau}(), false, false)
        pushchild!(father, newtableau)
        return newtableau
    end
end
Base.show(io::IO, t::LabeledTableau) = print(io, t.label)
@test_nowarn MetricHeap(randombranch)
@test_nowarn MetricHeap(distancefromroot)
@test_nowarn MetricHeap(inversedistancefromroot)
metricheaps = [
    MetricHeap(randombranch),
    MetricHeap(distancefromroot),
    MetricHeap(inversedistancefromroot)
]

################################################################################
# Core operations ##############################################################
################################################################################
#       t0
#      /  \
#    t1    t2
#   /  \
# t3    t4
################################################################################
t0 = LabeledTableau("t0", )
t1 = LabeledTableau("t1", t0)
t2 = LabeledTableau("t2", t0)
t3 = LabeledTableau("t3", t1)
t4 = LabeledTableau("t4", t1)
push!(metricheaps, t0)
push!(metricheaps, t1)
push!(metricheaps, t2)
push!(metricheaps, t3)
push!(metricheaps, t4)

@test tableau(first(heap(metricheaps[3]).valtree)) == t3 ||
      tableau(first(heap(metricheaps[3]).valtree)) == t4
@test metricvalue(first(heap(metricheaps[3]).valtree)) == -2
@test_nowarn roundrobin!(metricheaps, 3)
@test tableau(first(heap(metricheaps[3]).valtree)) == t3 ||
      tableau(first(heap(metricheaps[3]).valtree)) == t4
@test metricvalue(first(heap(metricheaps[3]).valtree)) == -2
@test_nowarn roundrobin!(metricheaps, 3)
@test tableau(first(heap(metricheaps[3]).valtree)) == t1 ||
      tableau(first(heap(metricheaps[3]).valtree)) == t2
@test metricvalue(first(heap(metricheaps[3]).valtree)) == -1

@test tableau(first(heap(metricheaps[2]).valtree)) == t0
@test metricvalue(first(heap(metricheaps[2]).valtree)) == 0
@test roundrobin!(metricheaps, 2) == t0
@test tableau(first(heap(metricheaps[2]).valtree)) == t1 ||
      tableau(first(heap(metricheaps[2]).valtree)) == t2
@test metricvalue(first(heap(metricheaps[2]).valtree)) == 1

@test_nowarn mostvoted!(metricheaps)
@test_nowarn mostvoted!(metricheaps, 42)

# Reset metricheaps
metricheaps = [
    MetricHeap(distancefromroot),
    MetricHeap(inversedistancefromroot),
    MetricHeap(distancefromroot)
]
push!(metricheaps, t0)
push!(metricheaps, t1)
push!(metricheaps, t2)
push!(metricheaps, t3)
push!(metricheaps, t4)

expand!(t0)
expand!(t2)
close!(t1)
@test roundrobin!(metricheaps, 42) == t2        # satisfiable branch
close!(t2)
@test isnothing(roundrobin!(metricheaps, 42))   # closed tableau

# Reset tableaux and metricheaps
t0 = LabeledTableau("t0", )
t1 = LabeledTableau("t1", t0)
t2 = LabeledTableau("t2", t0)
t3 = LabeledTableau("t3", t1)
t4 = LabeledTableau("t4", t1)
metricheaps = [
    MetricHeap(distancefromroot),
    MetricHeap(inversedistancefromroot),
    MetricHeap(distancefromroot)
]
push!(metricheaps, t0)
push!(metricheaps, t1)
push!(metricheaps, t2)
push!(metricheaps, t3)
push!(metricheaps, t4)

@test mostvoted!(metricheaps) == t0
expand!(t0)
expand!(t2)
close!(t1)
@test mostvoted!(metricheaps, 42) == t2        # satisfiable branch
close!(t2)
@test isnothing(mostvoted!(metricheaps, 42))   # closed tableau
