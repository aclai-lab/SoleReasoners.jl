```@meta
CurrentModule = SoleReasoners
```

```@contents
Pages = ["examples.md"]
```

# [Examples](@id examples)

This page is a runnable playbook. The complete version is
[`examples/playground.jl`](https://github.com/aclai-lab/SoleReasoners.jl/blob/main/examples/playground.jl).
Run it from a checkout with `julia --project=. examples/playground.jl`.

## 1. Build formulas and run propositional SAT

```julia
using SoleReasoners
using SoleLogics: Atom, ∧, ∨, ¬

p, q = Atom.(["p", "q"])
sat(∧(p, ¬p))
sat(∨(p, q), roundrobin!, distancefromroot)
```

The first call is `false`; the second is `true`. `sat` is the propositional
solver, so its expansion rules cover atoms, Boolean constants, negation,
conjunction, disjunction and implication.

## 2. Use a finite many-valued algebra

```julia
using SoleReasoners
using SoleLogics: Atom, ∧, →, ⊤
using SoleLogics.ManyValuedLogics: booleanalgebra, G3, α

p, q = Atom.(["p", "q"])
alphasat(MVLTLFPTableau, ⊤, ∧(p, q), booleanalgebra)
alphaval(MVLTLFPTableau, α, →(p, p), G3)
```

The threshold must belong to the chosen algebra. In the Boolean algebra, use
`⊤` (not the `α` truth value from `G3`).

## 3. Run all supported tableau families

```julia
for tableau in (MVLTLFPTableau, MVCLTableau, MVHSTableau, MVLRCC8Tableau)
    @show tableau alphasat(tableau, ⊤, ∧(p, q), booleanalgebra)
end
```

The tableau type determines the temporal, compass, interval, or RCC8 frame
construction; the decision-procedure call remains the same.

## 4. Add a temporal/modal operator and a timeout

```julia
using SoleLogics: box, LTLFP_F
future_p = box(LTLFP_F)(p)
alphasat(MVLTLFPTableau, ⊤, future_p, booleanalgebra; timeout=10)
```

`timeout` is important when exploring formulas whose finite-frame search may
be expensive. A result of `nothing` means the search was interrupted, not that
the formula failed.

## 5. Select a deterministic expansion policy

```julia
alphasat(MVLTLFPTableau, ⊤, ∧(p, q), booleanalgebra,
         roundrobin!, distancefromroot; timeout=10)
```

`roundrobin!` prevents starvation while `distancefromroot` prefers shallow
nodes. `inversedistancefromroot` prefers deep nodes; `randombranch` supplies
random priorities. `mostvoted!` is available when a voting policy is desired.

## 6. Convert input formats

```julia
using SoleLogics: parseformula
sat(parseformula("(p ∨ q) ∧ ¬p"))
# sat(dimacstosole("problem.cnf"))
```

`dimacstosole` takes a path to a DIMACS CNF file. The utility currently parses
DIMACS into a SoleLogics formula; it does not write DIMACS files.

## What the results mean

- `sat` returns `Bool`.
- `alphasat` returns `true`/`false` for a completed search and `nothing` for a
  timeout or memory-guard abort.
- `alphaval` returns the corresponding validity result and propagates
  `nothing` when its search is interrupted.

The source does not state a general decidable fragment or a universal
termination/completeness guarantee for the modal tableau families. Use the
finite algebra and `timeout` deliberately, and treat `nothing` as unknown.
