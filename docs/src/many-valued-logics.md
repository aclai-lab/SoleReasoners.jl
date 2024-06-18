```@meta
CurrentModule = SoleReasoners
```

```@contents
Pages = ["many-valued-logics.md"]
```

# [Many-Valued logics](@id man-core)

In addition to *sat* and *prove*, *SoleReasoners* also provides methods to deal with their many-valued couterparts, respectively *alphasat* and *alphaprove*. The former aims at solving the $\alpha$-satisfiability problem, i.e., if there exists a model such that a given many-valued formula assumes value of at least $\alpha$, while the latter aims at solving the $\alpha$-validity problem, i.e., if there is not a model for which a given many-valued formula does not assume value of at least $\alpha$.

For more information about the data structures involved, please refer to the developer documentation.

## ($\alpha$-)SAT solver

```@docs
sat(
    z::Formula,
    h::A;
    rng = Random.GLOBAL_RNG,
    verbose::Bool=false,
    timeout::Union{Nothing,Int}=nothing,
    kwargs...
) where {
    T<:Truth,
    D<:AbstractVector{T},
    A<:FiniteAlgebra{T,D}
}
alphasat(
        α::T1,
        z::Formula,
        a::A;
        rng = Random.GLOBAL_RNG,
        verbose::Bool=false,
        timeout::Union{Nothing,Int}=nothing,
        kwargs...
    ) where {
        T<:Truth,
        D<:AbstractVector{T},
        A<:FiniteAlgebra{T,D},
        T1<:Truth
    }
```

## Automated theorem ($\alpha$-)prover
```@docs
prove(
        z::Formula,
        h::A;
        rng = Random.GLOBAL_RNG,
        verbose::Bool=false,
        timeout::Union{Nothing,Int}=nothing,
        kwargs...
    ) where {
        T<:Truth,
        D<:AbstractVector{T},
        A<:FiniteAlgebra{T,D}
    }
alphaprove(
        α::T1,
        z::Formula,
        a::A;
        rng = Random.GLOBAL_RNG,
        verbose::Bool=false,
        timeout::Union{Nothing,Int}=nothing,
        kwargs...
    ) where {
        T<:Truth,
        D<:AbstractVector{T},
        A<:FiniteAlgebra{T,D},
        T1<:Truth
    }
```
