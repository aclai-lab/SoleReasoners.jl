```@meta
CurrentModule = SoleReasoners
```

# [Getting started](@id man-core)

In this introductory section you will learn about the main building blocks of SoleReasoners. Their definition, usage examples and how to customize them to your own needings. 

## Tableau

```@docs
Tableau
φ(tableau::Tableau)::Formula = tableau.φ
fatherset(tableau::Tableau)::Set{Tableau}
father(tableau::Tableau)::Union{Tableau, Nothing}
childrenset(tableau::Tableau)::Set{Tableau}
literals(tableau::Tableau)::Set{Formula}
leaves(leavesset::Set{Tableau}, tableau::Tableau)::Set{Tableau}
leaves(tableau::Tableau)::Set{Tableau}
pushfather!(tableau::Tableau, newfather::Tableau)::Set{Tableau}
popfather!(tableau::Tableau)::Tableau
pushchildren!(tableau::Tableau, children::Tableau...)::Set{Tableau}
pushliterals!(tableau::Tableau, newliterals::Formula...)::Set{Formula}
findroot(tableau::Tableau)::Tableau
isleaf(tableau::Tableau)::Bool 
```

## MetricHeapNode

```@docs
MetricHeapNode
metricvalue(metricheapnode::MetricHeapNode)
tableau(metricheapnode::MetricHeapNode)
```

## MetricHeapOrdering

```@docs
MetricHeapOrdering
lt(o::MetricHeapOrdering, a::MetricHeapNode, b::MetricHeapNode)::Bool
```

## MetricHeap

```@docs
MetricHeap
heap(metricheap::MetricHeap)::BinaryHeap{MetricHeapNode}
metric(metricheap::MetricHeap)::Function
push!(metricheap::MetricHeap, metricheapnode::MetricHeapNode)::BinaryHeap{MetricHeapNode}
push!(metricheap::MetricHeap, tableau::Tableau)::BinaryHeap{MetricHeapNode}
pop!(metricheap::MetricHeap)::Tableau
isempty(metricheap::MetricHeap)::Bool
```

## SAT

```@docs
naivechooseleaf(metricheaps::Vector{MetricHeap})::Union{Tableau, Nothing}
naivechooseleaf(metricheaps::Vector{MetricHeap}, cycle::Int)
roundrobin(metricheaps::Vector{MetricHeap}, cycle::Int)::Union{Tableau, Nothing}
push!(metricheaps::Set{MetricHeap}, tableau::Tableau)::Nothing
push!(metricheaps::Vector{MetricHeap}, tableau::Tableau)::Nothing
sat(metricheaps::Vector{MetricHeap}, chooseleaf::Function)::Bool
sat(φ::Formula, chooseleaf::Function, metrics::Function...)::Bool
sat(φ::Formula, chooseleaf::Function; rng = Random.GLOBAL_RNG)::Bool
sat(φ::Formula; rng = Random.GLOBAL_RNG)::Bool
```

## Utils

```@docs
dimacstosole(dimacscnf::String)::Formula
```
