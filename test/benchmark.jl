using BenchmarkTools
using Random
using SoleLogics
using SoleLogics.ManyValuedLogics
using SoleReasoners
using Test

# include("algebras/g3.jl")
# println(sat(parseformula("p∧(p→⊥)"), G3))

const BASE_MANY_VALUED_CONNECTIVES = [∨, ∧, →]
const BaseManyValuedConnectives = Union{typeof.(BASE_MANY_VALUED_CONNECTIVES)...}

myalphabet = Atom.(["p", "q"])

############################################################################################
#### G4 ####################################################################################
############################################################################################

include("algebras/g4.jl")
myoperators4 = []
append!(myoperators4, BASE_MANY_VALUED_CONNECTIVES)
append!(myoperators4, d4)
opweights4 = [10, 10, 10, 1, 1, 1, 1]

# for i ∈ 1:50
#     @test alphasat(
#         rand(MersenneTwister(i), d4),
#         randformula(MersenneTwister(i), 5, myalphabet, myoperators4, opweights=opweights4),
#         G4
#     ) == alphasat(
#         rand(MersenneTwister(i), d4),
#         randformula(MersenneTwister(i), 5, myalphabet, myoperators4, opweights=opweights4),
#         FiniteHeytingAlgebra(G4)
#     )
# end

rng = MersenneTwister(1234)
display(
    @benchmark alphasat(
        rand(rng, d4),
        randformula(rng, 6, myalphabet, myoperators4, opweights=opweights4),
        G4
    )
)

# rng = MersenneTwister(1234)
# display(
#     @benchmark alphasat(
#         rand(rng, d4),
#         randformula(rng, 5, myalphabet, myoperators4, opweights=opweights4),
#         FiniteHeytingAlgebra(G4)
#     )
# )

############################################################################################
#### H4 ####################################################################################
############################################################################################

# include("algebras/h4.jl")

# for i ∈ 1:50
#     @test alphasat(
#         rand(MersenneTwister(i), d4),
#         randformula(MersenneTwister(i), 8, myalphabet, myoperators4, opweights=opweights4),
#         H4
#     ) == alphasat(
#         rand(MersenneTwister(i), d4),
#         randformula(MersenneTwister(i), 8, myalphabet, myoperators4, opweights=opweights4),
#         FiniteHeytingAlgebra(H4)
#     )
# end

# rng = MersenneTwister(1234)
# display(
#     @benchmark alphasat(
#         rand(rng, d4),
#         randformula(rng, 6, myalphabet, myoperators4, opweights=opweights4),
#         H4
#     )
# )

# rng = MersenneTwister(1234)
# display(
#     @benchmark alphasat(
#         rand(rng, d4),
#         randformula(rng, 6, myalphabet, myoperators4, opweights=opweights4),
#         FiniteHeytingAlgebra(H4)
#     )
# )

############################################################################################
#### H9 ####################################################################################
############################################################################################

# include("algebras/h9.jl")
# myoperators9 = []
# append!(myoperators9, BASE_MANY_VALUED_CONNECTIVES)
# append!(myoperators9, d9)
# opweights9 = [10, 10, 10, 1, 1, 1, 1, 1, 1, 1, 1, 1]

# for i ∈ 1:50
#     @test alphasat(
#         rand(MersenneTwister(i), d9),
#         randformula(MersenneTwister(i), 8, myalphabet, myoperators9, opweights=opweights9),
#         H9
#     ) == alphasat(
#         rand(MersenneTwister(i), d9),
#         randformula(MersenneTwister(i), 8, myalphabet, myoperators9, opweights=opweights9),
#         FiniteHeytingAlgebra(H9)
#     )
# end

# rng = MersenneTwister(1234)
# display(
#     @benchmark alphasat(
#         rand(rng, d9),
#         randformula(rng, 6, myalphabet, myoperators9, opweights=opweights9),
#         H9
#     )
# )

# rng = MersenneTwister(1234)
# display(
#     @benchmark alphasat(
#         rand(rng, d9),
#         randformula(rng, 6, myalphabet, myoperators9, opweights=opweights9),
#         FiniteHeytingAlgebra(H9)
#     )
# )
