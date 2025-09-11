```@meta
CurrentModule = SoleReasoners
```

```@contents
Pages = ["getting-started.md"]
```

# [Getting started](@id man-core)

*SoleReasoners* mainly provides two tools for reasoning: *alphasat*, which aims at solving the $\alpha$-satisfiability problem, a relaxation of the [boolean satisfiability problem](https://en.wikipedia.org/wiki/Boolean_satisfiability_problem) for many-valued logic asking if an interpretation satisfies a formula with value at least $alpha$, and *alphaval*, which serves as an [automated theorem prover](https://en.wikipedia.org/wiki/Automated_theorem_proving) solving the $\alpha$-validity problem, a relaxation of the validity problem for many-valued logic asking if a formula is satisfied by any interpretation with value at least $\alpha$. Both algorithms are based on the [method of analytic tableaux](https://en.wikipedia.org/wiki/Method_of_analytic_tableaux).

*SoleReasoners* also provides a suite for managing the tableau expansion policy, allowing for different configurations based on the specific application problem. This system is based on min-heaps concurring to provide candidates for the extraction based on user specified policies, and an agreement function to choose amongst such proposals.

## SAT solver

```@docs
alphasat(
    ::T,
    α::T1,
    φ::Formula,
    algebra::FiniteFLewAlgebra,
    choosenode::Function,
    metrics::Function...;
    kwargs...
) where {
    T<:ManyValuedMultiModalTableau,
    T1<:Truth
}
```

## Automated theorem prover
```@docs
alphaval(
    ::T,
    α::T1,
    φ::Formula,
    algebra::FiniteFLewAlgebra,
    choosenode::Function,
    metrics::Function...;
    kwargs...
) where {
    T<:ManyValuedMultiModalTableau,
    T1<:Truth
}
```
