```@meta
CurrentModule = SoleReasoners
```

```@contents
Pages = ["getting-started.md"]
```

# [Getting started](@id man-core)

In this introductory section you will learn about the main building blocks of SoleReasoners. Their definition, usage examples and how to customize them to your own needings. 

## Tableau

```@docs
Tableau
φ(tableau::Tableau)
fatherset(tableau::Tableau)
father(tableau::Tableau)
childrenset(tableau::Tableau)
literals(tableau::Tableau)
leaves(leavesset::Set{Tableau}, tableau::Tableau)
leaves(tableau::Tableau)
pushfather!(tableau::Tableau, newfather::Tableau)
popfather!(tableau::Tableau)
pushchildren!(tableau::Tableau, children::Tableau...)
pushliterals!(tableau::Tableau, newliterals::Formula...)
findroot(tableau::Tableau)
isleaf(tableau::Tableau) 
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
lt(o::MetricHeapOrdering, a::MetricHeapNode, b::MetricHeapNode)
```

## MetricHeap

```@docs
MetricHeap
heap(metricheap::MetricHeap)
metric(metricheap::MetricHeap)
push!(metricheap::MetricHeap, metricheapnode::MetricHeapNode)
push!(metricheap::MetricHeap, tableau::Tableau)
pop!(metricheap::MetricHeap)
isempty(metricheap::MetricHeap)
```

## SAT

```@docs
naivechooseleaf(metricheaps::Vector{MetricHeap})
naivechooseleaf(metricheaps::Vector{MetricHeap}, cycle::Int)
roundrobin(metricheaps::Vector{MetricHeap}, cycle::Int)
push!(metricheaps::Vector{MetricHeap}, tableau::Tableau)
sat(metricheaps::Vector{MetricHeap}, chooseleaf::Function)
sat(φ::Formula, chooseleaf::Function, metrics::Function...)
sat(φ::Formula, chooseleaf::Function; rng = Random.GLOBAL_RNG)
sat(φ::Formula; rng = Random.GLOBAL_RNG)
```
