using Random: rand, Xoshiro
using SoleReasoners: AbstractTableau, MetricHeap, cleanheaps!
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
rng = Xoshiro(42)
customrandombranch(_::LabeledTableau) = rand(rng, Int)
@test_nowarn MetricHeap(customrandombranch)

################################################################################
# Logger #######################################################################
################################################################################
metricheap = MetricHeap(customrandombranch)
b = IOBuffer()
print(b, metricheap)
@test String(take!(b)) == "Metric: customrandombranch\nBinaryHeap: " *
    "SoleReasoners.MetricHeapNode[]"

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
@test_nowarn push!(Vector{MetricHeap}([metricheap]), t0)
@test_nowarn push!(Vector{MetricHeap}([metricheap]), t1)
@test_nowarn push!(Vector{MetricHeap}([metricheap]), t2)
@test_nowarn push!(Vector{MetricHeap}([metricheap]), t3)
@test_nowarn push!(Vector{MetricHeap}([metricheap]), t4)
print(b, metricheap)
@test String(take!(b)) == "Metric: customrandombranch\nBinaryHeap: " *
    "SoleReasoners.MetricHeapNode[(-6837375653060620944, t0), " *
    "(-6025700052079004298, t4), (8806607393865937907, t2), " *
    "(8307287183603472652, t1), (-5476287698561453020, t3)]"

popped = pop!(metricheap)
@test popped == t0
print(b, metricheap)
@test String(take!(b)) == "Metric: customrandombranch\nBinaryHeap: " *
    "SoleReasoners.MetricHeapNode[(-6025700052079004298, t4), " *
    "(-5476287698561453020, t3), (8806607393865937907, t2), " *
    "(8307287183603472652, t1)]"

popped = pop!(metricheap)
@test popped == t4
print(b, metricheap)
@test String(take!(b)) == "Metric: customrandombranch\nBinaryHeap: " *
    "SoleReasoners.MetricHeapNode[(-5476287698561453020, t3), " *
    "(8307287183603472652, t1), (8806607393865937907, t2)]"

expand!(t1)
close!(t2)
expand!(t3)
@test_nowarn cleanheaps!(Vector{MetricHeap}([metricheap]))
print(b, metricheap)
@test String(take!(b)) == "Metric: customrandombranch\nBinaryHeap: " *
    "SoleReasoners.MetricHeapNode[(-5476287698561453020, t3)]"

close!(t3)
@test_nowarn cleanheaps!(Vector{MetricHeap}([metricheap]))
@test isempty(metricheap)
