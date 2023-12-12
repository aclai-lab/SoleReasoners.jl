# Reasoners

This package provides algorithms for reasoning, namely including a sat solver based on analytic tableau technique.

## Installation & Usage

Simply type the following commands in Julia's REPL

```julia
# Install package
using Pkg; Pkg.add("Reasoners");

# Import packages
using SoleLogics    # Needed to write formulas
using Random
using Reasoners

# Instantiate a formula
φ = parseformula("(x∨y∨z)∧(x∨y∨¬z)∧(x∨¬y∨z)∧(x∨¬y∨¬z)∧(¬x∨y∨z)∧(¬x∨y∨¬z)∧(¬x∨¬y∨z)∧(¬x∨¬y∨¬z)")   # false

# Instantiate one ore more metrics (functions taking as input a Tableau and giving as output an Int)
randombranch(tableau::Tableau) = rand(Random.GLOBAL_RNG, Int)

# Call sat con the formula
sat(φ, randombranch)
``````