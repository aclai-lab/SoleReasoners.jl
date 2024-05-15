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

using SoleLogics.ManyValuedLogics: H4
using SoleLogics.ManyValuedLogics: α, β
myoperators4 = []
append!(myoperators4, BASE_MANY_VALUED_CONNECTIVES)
append!(myoperators4, getdomain(H4))
opweights4 = [10, 10, 10, 1, 1, 1, 1]

for height in 1:max_height
    # println("Alphaprove on H4 formulas of height up to " * string(height) * "\n")
    for i in 1:max_it
        @test alphaprove(
        rand(MersenneTwister(i), getdomain(H4)),
        randformula(MersenneTwister(i), height, myalphabet, BASE_MANY_VALUED_CONNECTIVES),
        H4,
        timeout=max_timeout,
        # verbose=true
    ) == alphaprove(
        rand(MersenneTwister(i), getdomain(H4)),
        randformula(MersenneTwister(i), height, myalphabet, BASE_MANY_VALUED_CONNECTIVES),
        FiniteHeytingAlgebra(H4),
        timeout=max_timeout,
        # verbose=true
    )
    end
end