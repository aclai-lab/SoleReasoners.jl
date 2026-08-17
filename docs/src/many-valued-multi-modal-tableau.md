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

## Extractable certificates

`alphasat` returns `true`, `false`, or `nothing`. Called with the opt-in
`certificate=true` keyword, it additionally returns a certificate built out of
the tableau state the search already computes, so an independent checker can
validate the verdict without re-running the search:

```julia
result, cert = alphasat(MVHSTableau, α, φ, algebra; certificate=true)
```

- when `result` is `false`, `cert` is an [`UnsatCertificate`](@ref): one
  [`BranchClosure`](@ref) per branch the search closed, each naming which
  closure condition fired (`:X1`, `:X2`, `:X3`, `:X4`, `:X5`, or `:X5bis` —
  the many-valued conditions under which a branch closes; this is **not**
  Boolean `p`/`¬p` closure) together with the root-to-leaf trace that produced
  it;
- when `result` is `true`, `cert` is a [`SatCertificate`](@ref): the open
  branch as a model — the worlds it mentions, the `frame` it settled on (from
  which accessibility edges can be recomputed with `mveval`), and the
  root-to-leaf trace of truth assignments;
- when `result` is `nothing`, `cert` is an [`UndeterminedCertificate`](@ref),
  which records only that the search was cut short by timeout or memory. It
  is a distinct type from the other two, so a consumer cannot mistake
  "undetermined" for a proof of either verdict.

When `certificate` is omitted (or `false`), `alphasat` is unchanged: it
returns exactly `true`, `false`, or `nothing`, nothing more.

For a serialisable form, [`serialize_alphasat`](@ref) turns `(result, cert)`
into a plain nested `Dict{String,Any}` with a documented `"schema_version"`
key; no JSON dependency is added, callers serialise the `Dict` themselves.
The satisfiable certificate's frame is a nested dictionary containing the
`"lt"` and `"eq"` truth-value matrices (or component orders for a product
frame), rather than a Julia-specific frame object.

```@docs
TableauCertificate
BranchStep
BranchClosure
UnsatCertificate
SatCertificate
UndeterminedCertificate
branchstep(t::T) where {T<:ManyValuedMultiModalTableau}
branchsteps(t::T) where {T<:ManyValuedMultiModalTableau}
certificatedict(cert::UnsatCertificate)
serialize_alphasat(result::Union{Bool,Nothing}, cert::Union{Nothing,TableauCertificate})
```

Certificate support currently covers `alphasat` for all four tableau types
(`MVLTLFPTableau`, `MVCLTableau`, `MVHSTableau`, `MVLRCC8Tableau`); `alphaval`
does not accept `certificate` yet.

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
