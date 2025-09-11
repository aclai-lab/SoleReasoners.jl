```@meta
CurrentModule = SoleReasoners
```

```@contents
Pages = ["many-valued-multi-modal-tableau.md"]
```

# [Many-Valued Multi-Modal Tableau](@id man-core)

The necessary components to reason about many-valued multi-modal logic using an Analytic Tableaux Technique, suitable for both $\alpha$-satisfiability and $\alpha$-validity, i.e., the counterparts of classical (crisp) satisfiability and authomated theorem proving, asking that the evaluation of a formula $\varphi$ has value at least $\alpha$ for one  possible model in one possible world (resp, all possible models in all possible worlds). Classical satisfiability and validity are obtained setting $\alpha=1$.

```@docs
ManyValuedMultiModalTableau
judgement(t::T) where {T<:ManyValuedMultiModalTableau}
assertion(t::T) where {T<:ManyValuedMultiModalTableau}
world(t::T) where {T<:ManyValuedMultiModalTableau}
frame(t::T) where {T<:ManyValuedMultiModalTableau}
worlds(
    ::Type{T},
    frame::Union{ManyValuedLinearOrder, NTuple{2, ManyValuedLinearOrder}}
) where {
    T<:ManyValuedMultiModalTableau
}
newframes(
    t::T,
    algebra::FiniteFLewAlgebra
) where {
    T<:ManyValuedMultiModalTableau
}
Base.show(io::IO, t::T) where {T<:ManyValuedMultiModalTableau}
```

Each many-valued multi-modal logic is associated with a specific tableau
structure subtype of `ManyValuedMultiModalTableau`, and must comprise a
`judgement`, an `assertion`, a `world`, a `frame`, a `father`, an array of
`children`, and two flags `expanded` and `closed`.

Different subtypes of `ManyValuedMultiModalTableau` usually differ for the type
of `world` and `frame`, which can be either a `ManyValuedLinearOrder` or an
`NTuple{N,ManyValuedLinearOrder}`, as well as the recursive fields (i.e., 
`father` and `children`), sharing the same subtype of 
`ManyValuedMultiModalTableau`.

All structures will be digested by the same algorithms, parameterized on the
subtype of `ManyValuedMultiModalTableau`.

## A tableau for Many-Valued Linear Temporal Logic with Future and Past

```@docs
MVLTLFPTableau
```

## A tableau for Many-Valued Compass Logic

```@docs
MVCLTableau
```

## A tableau for Many-Valued Halpern and Shoham's modal logic of time

```@docs
MVHSTableau
```

## A tableau for Many-Valued Lutz and Wolter's modal logic of topological   relations with rectangular areas aligned with the axes

```@docs
MVLRCC8Tableau
```
