# Reasoners

This package provides algorithms for reasoning, namely including a sat solver based on analytic tableau technique.

## Installation & Usage

Simply type the following commands in Julia's REPL

"""
# Install package
using Pkg; Pkg.add("SoleLogics");
using Pkg; Pkg.add("Reasoners");

# Import packages
using SoleLogics
using Reasoners

# Instantiate a formula
φ = parseformula("p∧q")

# Call sat con the formula
sat(φ, height, ntokens, natoms)
"""