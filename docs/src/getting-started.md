```@meta
CurrentModule = SoleReasoners
```

```@contents
Pages = ["getting-started.md"]
```

# Getting started

SoleReasoners provides two decision procedures based on analytic tableaux:
`alphasat` checks α-satisfiability and `alphaval` checks α-validity. The
classical propositional procedure is `sat`. Formulas, atoms, truth values and
finite algebras are provided by SoleLogics.

## Install and make a formula

```julia
using Pkg
Pkg.add("SoleReasoners")

using SoleReasoners
using SoleLogics: Atom, ∧, ∨, →, ¬, ⊤
using SoleLogics.ManyValuedLogics: booleanalgebra

p, q = Atom.(["p", "q"])
φ = ∧(p, ¬q)
```

## Propositional SAT

`sat(φ)` returns `true` when the propositional formula has an open tableau
branch and `false` when every branch closes. The optional policy and metrics
make branch selection explicit:

```julia
sat(φ)
sat(∨(p, q), roundrobin!, distancefromroot)
```

For text input, use `SoleLogics.parseformula`; for a DIMACS CNF path, use
`dimacstosole`:

```julia
using SoleLogics: parseformula
sat(parseformula("(p ∨ q) ∧ ¬p"))
# sat(dimacstosole("problem.cnf"))
```

## α-satisfiability and α-validity

The short form constructs the initial tableau, metric heap and default policy:

```julia
alphasat(MVLTLFPTableau, ⊤, φ, booleanalgebra)
alphaval(MVLTLFPTableau, ⊤, →(p, p), booleanalgebra)
```

`α` is a truth value from the selected finite algebra, not necessarily a Julia
`Float64`. For a non-Boolean algebra, import its truth values and pass the
matching algebra, for example `alphaval(MVLTLFPTableau, α, →(p,p), G3)`.

All four exported tableau types can be passed to the same entry points:

```julia
for tableau in (MVLTLFPTableau, MVCLTableau, MVHSTableau, MVLRCC8Tableau)
    @show tableau alphasat(tableau, ⊤, ∧(p, q), booleanalgebra)
end
```

To bound finite-frame generation and expansion, pass `timeout` in seconds:

```julia
result = alphasat(MVLTLFPTableau, ⊤, φ, booleanalgebra; timeout=10)
```

A completed search returns `Bool`. `nothing` means that the timeout or the
implementation's memory guard stopped the search; it is not a negative answer.

## Supported tableau families

- `MVLTLFPTableau`: many-valued linear temporal logic with future and past.
- `MVCLTableau`: many-valued compass logic.
- `MVHSTableau`: many-valued Halpern--Shoham interval logic.
- `MVLRCC8Tableau`: many-valued Lutz--Wolter RCC8 rectangular logic.

Temporal, modal and relational operators are constructed in SoleLogics. For
example:

```julia
using SoleLogics: box, LTLFP_F
alphasat(MVLTLFPTableau, ⊤, box(LTLFP_F)(p), booleanalgebra; timeout=10)
```

## Running the playground

From a checkout, run the verified end-to-end script:

```sh
julia --project=. examples/playground.jl
```

The script exercises propositional SAT, all four tableau families, a
non-Boolean algebra, validity, a custom branch policy, and a temporal operator.

## [Known limitations](@id limitations)

The propositional `sat` implementation is separate from the many-valued
procedures. The latter enumerate and extend finite frames for the supported
tableau families, but the source does not state a general decidable fragment or
a universal termination/completeness guarantee. Use `timeout` when exploring.
A completed call returns `Bool`; `nothing` means timeout or the implementation's
memory guard stopped the search, not unsatisfiability or invalidity. No model,
proof, or certificate object is promised by the current return values.

## Exported API at a glance

`SoleReasoners` explicitly exports:

- `sat`, `alphasat`, `alphaval`: decision procedures;
- `MVLTLFPTableau`, `MVCLTableau`, `MVHSTableau`, `MVLRCC8Tableau`: tableau
  constructors/types;
- `roundrobin!`, `mostvoted!`: branch-selection policies;
- `randombranch`, `distancefromroot`, `inversedistancefromroot`, `formulaheight`:
  metrics;
- `booleantofuzzy`, `dimacstosole`: formula/file utilities.

Names such as `Atom`, `∧`, `box`, `booleanalgebra`, `G3`, and `α` belong to
SoleLogics and are imported separately. See [Examples](@ref examples) for a
runnable matrix of calls and [Known limitations](@ref limitations) before
using the procedures in production.

## SAT solver API

```@docs
sat(
    formula::Formula,
    choosenode::F,
    metrics::Function...
) where {F<:Function}
```

## Many-valued APIs

```@docs
alphasat(
    ::T,
    α::T1,
    φ::Formula,
    algebra::FiniteFLewAlgebra,
    choosenode::Function,
    metrics::Function...
) where {T<:ManyValuedMultiModalTableau, T1<:Truth}

alphaval(
    ::T,
    α::T1,
    φ::Formula,
    algebra::FiniteFLewAlgebra,
    choosenode::Function,
    metrics::Function...
) where {T<:ManyValuedMultiModalTableau, T1<:Truth}
```
