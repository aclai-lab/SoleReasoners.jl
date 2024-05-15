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

using SoleLogics.ManyValuedLogics: G4
using SoleLogics.ManyValuedLogics: α, β
myoperators4 = []
append!(myoperators4, BASE_MANY_VALUED_CONNECTIVES)
append!(myoperators4, getdomain(G4))
opweights4 = [10, 10, 10, 1, 1, 1, 1]

for height in 1:max_height
    # println("Alphasat on G4 formulas of height up to " * string(height) * "\n")
    for i in 1:max_it
        @test alphasat(
        rand(MersenneTwister(i), getdomain(G4)),
        randformula(MersenneTwister(i), height, myalphabet, BASE_MANY_VALUED_CONNECTIVES),
        G4,
        timeout=max_timeout,
        # verbose=true
    ) == alphasat(
        rand(MersenneTwister(i), getdomain(G4)),
        randformula(MersenneTwister(i), height, myalphabet, BASE_MANY_VALUED_CONNECTIVES),
        FiniteHeytingAlgebra(G4),
        timeout=max_timeout,
        # verbose=true
    )
    end
end