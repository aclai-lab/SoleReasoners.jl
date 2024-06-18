```@meta
CurrentModule = SoleReasoners
```

```@contents
Pages = ["getting-started.md"]
```

# [Getting started](@id man-core)

*SoleReasoners* mainly provides two tools for reasoning: *sat*, which aims at solving the [boolean satisfiability problem](https://en.wikipedia.org/wiki/Boolean_satisfiability_problem), and *prove*, which serves as an [automated theorem prover](https://en.wikipedia.org/wiki/Automated_theorem_proving) for propositional boolean formulae. Both algorithms are based on the [method of analytic tableaux](https://en.wikipedia.org/wiki/Method_of_analytic_tableaux).

*SoleReasoners* also provides a suite for managing the tableau expansion policy, allowing for different configurations based on the specific application problem. This system is based on min-heaps concurring to provide candidates for the extraction based on user specified policies, and an agreement function to choose amongst such proposals.

For more information about the data structures involved, please refer to the developer documentation.

## SAT solver

```@docs
sat(formula::Formula, chooseleaf::F, metrics::Function...) where {F<:Function}
sat(formula::Formula, metric::F; kwargs...) where {F<:Function}
sat(formula::Formula; rng = Random.GLOBAL_RNG, kwargs...)
```

## Automated theorem prover
```@docs
prove(formula::Formula, chooseleaf::F, metrics::Function...) where {F<:Function}
prove(formula::Formula, metric::F; kwargs...) where {F<:Function}
prove(formula::Formula; rng = Random.GLOBAL_RNG, kwargs...)
```
