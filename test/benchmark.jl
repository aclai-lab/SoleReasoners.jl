using BenchmarkTools
using Random
using SoleLogics
using SoleLogics.ManyValuedLogics
using SoleReasoners

const BASE_MANY_VALUED_CONNECTIVES = [∨, ∧, →]
const BaseManyValuedConnectives = Union{typeof.(BASE_MANY_VALUED_CONNECTIVES)...}

include("algebras/h4.jl")

myoperators = []
append!(myoperators, BASE_MANY_VALUED_CONNECTIVES)
append!(myoperators, d4)

myalphabet = Atom.(["p"])

for i ∈ 1:20
    alphasat(
        ⊥,
        randformula(Random.MersenneTwister(i), 1, myalphabet, myoperators),
        H4
    ) == alphasat(
        ⊥,
        randformula(Random.MersenneTwister(i), 1, myalphabet, myoperators),
        FiniteHeytingAlgebra(H4)
    )
    alphasat(
        α,
        randformula(Random.MersenneTwister(i), 1, myalphabet, myoperators),
        H4
    ) == alphasat(
        α,
        randformula(Random.MersenneTwister(i), 1, myalphabet, myoperators),
        FiniteHeytingAlgebra(H4)
    )
    alphasat(
        β,
        randformula(Random.MersenneTwister(i), 1, myalphabet, myoperators),
        H4
    ) == alphasat(
        β,
        randformula(Random.MersenneTwister(i), 1, myalphabet, myoperators),
        FiniteHeytingAlgebra(H4)
    )
    alphasat(
        ⊤,
        randformula(Random.MersenneTwister(i), 1, myalphabet, myoperators),
        H4
    ) == alphasat(
        ⊤,
        randformula(Random.MersenneTwister(i), 1, myalphabet, myoperators),
        FiniteHeytingAlgebra(H4)
    )
end

for i ∈ 1:20
    alphasat(
        ⊥,
        randformula(Random.MersenneTwister(i), 2, myalphabet, myoperators),
        H4
    ) == alphasat(
        ⊥,
        randformula(Random.MersenneTwister(i), 2, myalphabet, myoperators),
        FiniteHeytingAlgebra(H4)
    )
    alphasat(
        α,
        randformula(Random.MersenneTwister(i), 2, myalphabet, myoperators),
        H4
    ) == alphasat(
        α,
        randformula(Random.MersenneTwister(i), 2, myalphabet, myoperators),
        FiniteHeytingAlgebra(H4)
    )
    alphasat(
        β,
        randformula(Random.MersenneTwister(i), 2, myalphabet, myoperators),
        H4
    ) == alphasat(
        β,
        randformula(Random.MersenneTwister(i), 2, myalphabet, myoperators),
        FiniteHeytingAlgebra(H4)
    )
    alphasat(
        ⊤,
        randformula(Random.MersenneTwister(i), 2, myalphabet, myoperators),
        H4
    ) == alphasat(
        ⊤,
        randformula(Random.MersenneTwister(i), 2, myalphabet, myoperators),
        FiniteHeytingAlgebra(H4)
    )
end

display(
    @benchmark alphasat(
        ⊤,
        randformula(Random.MersenneTwister(rand((1,20))), 2, myalphabet, myoperators),
        H4
    )
)
display(
    @benchmark alphasat(
        ⊤,
        randformula(Random.MersenneTwister(rand((1,20))), 2, myalphabet, myoperators),
        FiniteHeytingAlgebra(H4)
    )
)
