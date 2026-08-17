# SoleReasoners.jl

[![Docs](https://img.shields.io/badge/docs-stable-blue.svg)](https://aclai-lab.github.io/SoleReasoners.jl/)
[![CI](https://github.com/aclai-lab/SoleReasoners.jl/actions/workflows/ci.yml/badge.svg)](https://github.com/aclai-lab/SoleReasoners.jl/actions/workflows/ci.yml)
[![codecov](https://codecov.io/gh/aclai-lab/SoleReasoners.jl/branch/main/graph/badge.svg?token=LT9IYIYNFI)](https://codecov.io/gh/aclai-lab/SoleReasoners.jl)

[SoleReasoners](https://github.com/aclai-lab/SoleReasoners.jl/) is a Julia package for [automated reasoning](https://en.wikipedia.org/wiki/Automated_reasoning) up to Many-Valued Multi-Modal Logic built on top of [SoleLogics.jl](https://github.com/aclai-lab/SoleLogics.jl/), and part of [Sole.jl](https://github.com/aclai-lab/Sole.jl), an open-source framework for symbolic machine learning.

## Installation

```julia
using Pkg
Pkg.add("SoleReasoners")
```

## Quick start: propositional SAT

Formulas are built with SoleLogics. `sat` returns a `Bool` for the classical
(propositional) tableau:

```julia
using SoleReasoners
using SoleLogics: Atom, ∧, ∨, ¬

p, q = Atom.(["p", "q"])
sat(∧(p, ¬p))                 # false
sat(∨(p, q))                  # true

# Choose a policy and one or more branch metrics explicitly.
sat(∨(p, q), roundrobin!, distancefromroot)
```

A formula can also be read from text with `SoleLogics.parseformula`, or from a
DIMACS CNF file with `dimacstosole`:

```julia
using SoleLogics: parseformula
sat(parseformula("(p ∨ q) ∧ ¬p"))
# sat(dimacstosole("problem.cnf"))
```

## Many-valued reasoning

`alphasat(TableauType, α, φ, algebra)` asks whether `φ` is satisfiable at
threshold `α`; `alphaval` asks whether it is valid at that threshold. The
short form uses `roundrobin!` and `randombranch`. In the Boolean algebra use
`⊤` as the threshold. Other finite algebras (such as `G3`) provide their own
truth values, including `α`.

```julia
using SoleReasoners
using SoleLogics: Atom, ∧, →, ⊤
using SoleLogics.ManyValuedLogics: booleanalgebra, G3, α

p, q = Atom.(["p", "q"])
alphasat(MVLTLFPTableau, ⊤, ∧(p, q), booleanalgebra) # true
alphaval(MVLTLFPTableau, α, →(p, p), G3)             # true
```

The four exported tableau types select the supported logic:

| Tableau type | Logic | Initial world/frame built by the solver |
| --- | --- | --- |
| `MVLTLFPTableau` | Many-Valued Linear Temporal Logic with future and past | a point and a linear order |
| `MVCLTableau` | Many-Valued Compass Logic | a 2-D point and two linear orders |
| `MVHSTableau` | Many-Valued Halpern--Shoham interval logic | an interval and a linear order |
| `MVLRCC8Tableau` | Many-Valued Lutz--Wolter RCC8 rectangular logic | a rectangle and two linear orders |

For example, the same Boolean formula can be checked with every tableau
implementation (each call was run against the package):

```julia
for tableau in (MVLTLFPTableau, MVCLTableau, MVHSTableau, MVLRCC8Tableau)
    @show tableau alphasat(tableau, ⊤, ∧(p, q), booleanalgebra)
end
```

Modal and temporal operators come from SoleLogics. For example, this is a
future-box formula for the LTL-with-future-and-past tableau:

```julia
using SoleLogics: box, LTLFP_F
alphasat(MVLTLFPTableau, ⊤, box(LTLFP_F)(p), booleanalgebra; timeout=10)
```

See [`examples/playground.jl`](examples/playground.jl) for a complete script
that can be run with `julia --project=. examples/playground.jl`.

## How to choose a tableau policy

A policy receives the metric heaps and the current expansion cycle. The
recommended starvation-free policy is `roundrobin!`; `mostvoted!` selects the
candidate occurring at the head of most heaps. A metric receives a tableau
node and returns an integer. Built-in metrics are `randombranch`,
`distancefromroot`, `inversedistancefromroot`, and `formulaheight` (the last is
for many-valued tableaux). Pass a deterministic metric when reproducibility
matters, for example:

```julia
using SoleReasoners: roundrobin!, distancefromroot
alphasat(MVLTLFPTableau, ⊤, ∧(p, q), booleanalgebra,
         roundrobin!, distancefromroot; timeout=10)
```

## Exported API

These are the names exported by `SoleReasoners` (the list is derived from
`src/SoleReasoners.jl`):

- **Decision procedures:** `sat` (propositional satisfiability), `alphasat`
  (many-valued α-satisfiability), and `alphaval` (many-valued α-validity).
- **Tableau constructors:** `MVLTLFPTableau`, `MVCLTableau`, `MVHSTableau`, and
  `MVLRCC8Tableau`.
- **Expansion policies:** `roundrobin!` and `mostvoted!`.
- **Metrics:** `randombranch`, `distancefromroot`, `inversedistancefromroot`,
  and `formulaheight`.
- **Utilities:** `booleantofuzzy` (replace Boolean negation by implication to
  bottom) and `dimacstosole` (read a DIMACS CNF path as a SoleLogics formula).

Formula constructors, atoms, truth values, finite algebras, and modal
relations are supplied by [SoleLogics.jl](https://github.com/aclai-lab/SoleLogics.jl)
and [SoleLogics.ManyValuedLogics]. They are intentionally not repeated as
SoleReasoners exports.

## Known limitations and result meanings

- `sat` is the propositional tableau implementation. Its expansion rules are
  for atoms, Boolean truth constants, `¬`, `∨`, `∧`, and `→`; it is not the
  many-valued/modal decision procedure.
- The many-valued procedures operate on the four tableau families above and
  finite `FiniteFLewAlgebra` instances. A timeout is available as
  `timeout=<seconds>`.
- `alphasat` and `alphaval` return `Bool` when the search finishes. They return
  `nothing` on timeout or when the implementation's memory guard aborts the
  search. Do not interpret `nothing` as unsatisfiable or invalid.
- The source defines the tableau rules and finite-frame generation, but does
  not state a general decidable fragment or a completeness/termination bound
  for every supported modal logic. That limit is therefore intentionally
  unstated here rather than guessed; use a timeout for exploratory searches.
- The current procedures return only the decision result. They do not promise
  a model, proof, or certificate object.

## About

The package is developed by the [ACLAI Lab](https://aclai.unife.it/en/) @ University of Ferrara.

## More on Sole
- [SoleLogics](https://github.com/aclai-lab/SoleLogics.jl/)
- [SoleData.jl](https://github.com/aclai-lab/SoleData.jl)
- [SoleModels.jl](https://github.com/aclai-lab/SoleModels.jl)
- [SolePostHoc.jl](https://github.com/aclai-lab/SolePostHoc.jl)
