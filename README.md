# SoleReasoners.jl

[![Dev](https://img.shields.io/badge/docs-dev-blue.svg)](https://aclai-lab.github.io/SoleReasoners.jl/dev)
[![Build Status](https://api.cirrus-ci.com/github/aclai-lab/SoleReasoners.jl.svg?branch=main)](https://cirrus-ci.com/github/aclai-lab/SoleReasoners.jl)
[![codecov](https://codecov.io/gh/aclai-lab/SoleReasoners.jl/branch/main/graph/badge.svg?token=LT9IYIYNFI)](https://codecov.io/gh/aclai-lab/SoleReasoners.jl)

[SoleReasoners](https://github.com/aclai-lab/SoleReasoners.jl/) is a Julia package for [automated reasoning](https://en.wikipedia.org/wiki/Automated_reasoning) built on top of [SoleLogics.jl](https://github.com/aclai-lab/SoleLogics.jl/), and part of [Sole.jl](https://github.com/aclai-lab/Sole.jl), an open-source framework for symbolic machine learning.

## Installation

To install SoleReasoners.jl, use the Julia package manager:
```julia
using Pkg
Pkg.add("SoleReasoners")
```

## Feature Summary

SoleReasoners.jl provides a [SAT solver](https://en.wikipedia.org/wiki/SAT_solver) and an [automated theorem prover](https://en.wikipedia.org/wiki/Automated_theorem_proving) based on the [method of analytic tableaux](https://en.wikipedia.org/wiki/Method_of_analytic_tableaux). 

It also provides a Many-Valued version for both algorithms, therefore solving the $\alpha$-satisfiability and $\alpha$-validity problems respectively.

## Future work

We are currently working on a modal version of both algorithms which also works with Many-Valued logics.

## About

The package is developed by the [ACLAI Lab](https://aclai.unife.it/en/) @ University of Ferrara.

## More on Sole
- [SoleLogics](https://github.com/aclai-lab/SoleLogics.jl/)
- [SoleData.jl](https://github.com/aclai-lab/SoleData.jl)
- [SoleFeatures.jl](https://github.com/aclai-lab/SoleFeatures.jl) 
- [SoleModels.jl](https://github.com/aclai-lab/SoleModels.jl)
- [SolePostHoc.jl](https://github.com/aclai-lab/SolePostHoc.jl)
