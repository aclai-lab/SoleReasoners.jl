using BenchmarkTools
using Random
using SoleLogics
using SoleLogics.ManyValuedLogics
using SoleReasoners
using Test

BASE_MANY_VALUED_CONNECTIVES = [∨, ∧, →]
BaseManyValuedConnectives = Union{typeof.(BASE_MANY_VALUED_CONNECTIVES)...}

myalphabet = Atom.(["p"])

max_height = 4
max_it = 1000
max_timeout = 60 # seconds

using SoleLogics.ManyValuedLogics: booleanalgebra
myoperators2 = []
append!(myoperators2, BASE_MANY_VALUED_CONNECTIVES)
append!(myoperators2, getdomain(booleanalgebra))
opweights4 = [10, 10, 10, 1, 1]

for height in 1:max_height
    # println("Alphaprove on booleanalgebra formulas of height up to " * string(height) * "\n")
    for i in 1:max_it
        @test alphaprove(
        rand(MersenneTwister(i), getdomain(booleanalgebra)),
        randformula(MersenneTwister(i), height, myalphabet, BASE_MANY_VALUED_CONNECTIVES),
        booleanalgebra,
        timeout=max_timeout,
        # verbose=true
    ) == alphaprove(
        rand(MersenneTwister(i), getdomain(booleanalgebra)),
        randformula(MersenneTwister(i), height, myalphabet, BASE_MANY_VALUED_CONNECTIVES),
        FiniteHeytingAlgebra(booleanalgebra),
        timeout=max_timeout,
        # verbose=true
    )
    end
end