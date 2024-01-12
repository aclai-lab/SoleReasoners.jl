# SoleReasoners.jl

[![Build Status](https://api.cirrus-ci.com/github/aclai-lab/SoleReasoners.jl.svg?branch=main)](https://cirrus-ci.com/github/aclai-lab/SoleReasoners.jl)
[![codecov](https://codecov.io/gh/aclai-lab/SoleReasoners.jl/branch/main/graph/badge.svg?token=LT9IYIYNFI)](https://codecov.io/gh/aclai-lab/SoleReasoners.jl)
[![Binder](https://mybinder.org/badge_logo.svg)](https://mybinder.org/v2/gh/aclai-lab/SoleReasoners.jl/HEAD?labpath=pluto-demo.jl)

This package provides algorithms for reasoning, namely including a sat solver based on analytic tableau technique.

## Installation & Usage

Simply type the following commands in Julia's REPL

```julia
# Install package
using Pkg; Pkg.add("Reasoners");

# Import packages
using Random
using Reasoners

# Instantiate a formula (syntax based on the SoleLogics package)
φ = parseformula("(x∨y∨z)∧(x∨y∨¬z)∧(x∨¬y∨z)∧(x∨¬y∨¬z)∧(¬x∨y∨z)∧(¬x∨y∨¬z)∧(¬x∨¬y∨z)∧(¬x∨¬y∨¬z)")   # false

# Instantiate one ore more metrics (functions taking as input a Tableau and giving as output an Int)
randombranch(tableau::Tableau) = rand(Random.GLOBAL_RNG, Int)

# Call sat con the formula
sat(φ, randombranch)
``````
