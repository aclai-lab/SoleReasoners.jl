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
max_timeout = 120 # seconds

using SoleLogics.ManyValuedLogics: H9
using SoleLogics.ManyValuedLogics: α, β, γ, δ, ε, ζ, η
myoperators9 = []
append!(myoperators9, BASE_MANY_VALUED_CONNECTIVES)
append!(myoperators9, getdomain(H9))
opweights4 = [10, 10, 10, 1, 1, 1, 1, 1, 1, 1, 1, 1]

for height in 1:max_height
    # println("Alphaprove on H9 formulas of height up to " * string(height) * "\n")
    for i in 1:max_it
        @test alphaprove(
        rand(MersenneTwister(i), getdomain(H9)),
        randformula(MersenneTwister(i), height, myalphabet, BASE_MANY_VALUED_CONNECTIVES),
        H9,
        timeout=max_timeout,
        # verbose=true
    ) == alphaprove(
        rand(MersenneTwister(i), getdomain(H9)),
        randformula(MersenneTwister(i), height, myalphabet, BASE_MANY_VALUED_CONNECTIVES),
        FiniteHeytingAlgebra(H9),
        timeout=max_timeout,
        # verbose=true
    )
    end
end