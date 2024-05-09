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

# ############################################################################################
# #### BooleanAlgebra ########################################################################
# ############################################################################################

# using SoleLogics.ManyValuedLogics: booleanalgebra
# myoperators2 = []
# append!(myoperators2, BASE_MANY_VALUED_CONNECTIVES)
# append!(myoperators2, getdomain(booleanalgebra))
# opweights4 = [10, 10, 10, 1, 1]

# for height in 1:max_height
#     println("Alphasat on booleanalgebra formulas of height up to " * string(height) * "\n")
#     for i in 1:max_it
#         @test alphasat(
#         rand(MersenneTwister(i), getdomain(booleanalgebra)),
#         randformula(MersenneTwister(i), height, myalphabet, BASE_MANY_VALUED_CONNECTIVES),
#         booleanalgebra,
#         timeout=max_timeout,
#         # verbose = true
#     ) == alphasat(
#         rand(MersenneTwister(i), getdomain(booleanalgebra)),
#         randformula(MersenneTwister(i), height, myalphabet, BASE_MANY_VALUED_CONNECTIVES),
#         FiniteHeytingAlgebra(booleanalgebra),
#         timeout=max_timeout,
#         # oldrule=true
#     )
#     end
#     println("Alphaprove on booleanalgebra formulas of height up to " * string(height) * "\n")
#     for i in 1:max_it
#         @test alphaprove(
#         rand(MersenneTwister(i), getdomain(booleanalgebra)),
#         randformula(MersenneTwister(i), height, myalphabet, BASE_MANY_VALUED_CONNECTIVES),
#         booleanalgebra,
#         timeout=max_timeout,
#         # verbose = true
#     ) == alphaprove(
#         rand(MersenneTwister(i), getdomain(booleanalgebra)),
#         randformula(MersenneTwister(i), height, myalphabet, BASE_MANY_VALUED_CONNECTIVES),
#         FiniteHeytingAlgebra(booleanalgebra),
#         timeout=max_timeout,
#         # oldrule=true
#     )
#     end
# end

# ############################################################################################
# #### G3 ####################################################################################
# ############################################################################################

# using SoleLogics.ManyValuedLogics: G3
# myoperators3 = []
# append!(myoperators3, BASE_MANY_VALUED_CONNECTIVES)
# append!(myoperators3, getdomain(G3))
# opweights4 = [10, 10, 10, 1, 1, 1]

# for height in 1:max_height
#     println("Alphasat on G3 formulas of height up to " * string(height) * "\n")
#     for i in 1:max_it
#         @test alphasat(
#         rand(MersenneTwister(i), getdomain(G3)),
#         randformula(MersenneTwister(i), height, myalphabet, BASE_MANY_VALUED_CONNECTIVES),
#         G3,
#         timeout=max_timeout
#         # verbose = true
#     ) == alphasat(
#         rand(MersenneTwister(i), getdomain(G3)),
#         randformula(MersenneTwister(i), height, myalphabet, BASE_MANY_VALUED_CONNECTIVES),
#         FiniteHeytingAlgebra(G3),
#         timeout=max_timeout,
#         # oldrule=true
#     )
#     end
#     println("Alphaprove on G3 formulas of height up to " * string(height) * "\n")
#     for i in 1:max_it
#         @test alphaprove(
#         rand(MersenneTwister(i), getdomain(G3)),
#         randformula(MersenneTwister(i), height, myalphabet, BASE_MANY_VALUED_CONNECTIVES),
#         G3,
#         timeout=max_timeout
#         # verbose = true
#     ) == alphaprove(
#         rand(MersenneTwister(i), getdomain(G3)),
#         randformula(MersenneTwister(i), height, myalphabet, BASE_MANY_VALUED_CONNECTIVES),
#         FiniteHeytingAlgebra(G3),
#         timeout=max_timeout,
#         # oldrule=true
#     )
#     end
# end

# ############################################################################################
# #### G4 ####################################################################################
# ############################################################################################

# using SoleLogics.ManyValuedLogics: G4
# using SoleLogics.ManyValuedLogics: α, β
# myoperators4 = []
# append!(myoperators4, BASE_MANY_VALUED_CONNECTIVES)
# append!(myoperators4, getdomain(G4))
# opweights4 = [10, 10, 10, 1, 1, 1, 1]

# for height in 1:max_height
#     println("Alphasat on G4 formulas of height up to " * string(height) * "\n")
#     for i in 1:max_it
#         @test alphasat(
#         rand(MersenneTwister(i), getdomain(G4)),
#         randformula(MersenneTwister(i), height, myalphabet, BASE_MANY_VALUED_CONNECTIVES),
#         G4,
#         timeout=max_timeout,
#         # verbose = true
#     ) == alphasat(
#         rand(MersenneTwister(i), getdomain(G4)),
#         randformula(MersenneTwister(i), height, myalphabet, BASE_MANY_VALUED_CONNECTIVES),
#         FiniteHeytingAlgebra(G4),
#         timeout=max_timeout
#     )
#     end
#     println("Alphaprove on G4 formulas of height up to " * string(height) * "\n")
#     for i in 1:max_it
#         @test alphaprove(
#         rand(MersenneTwister(i), getdomain(G4)),
#         randformula(MersenneTwister(i), height, myalphabet, BASE_MANY_VALUED_CONNECTIVES),
#         G4,
#         timeout=max_timeout
#         # verbose = true
#     ) == alphaprove(
#         rand(MersenneTwister(i), getdomain(G4)),
#         randformula(MersenneTwister(i), height, myalphabet, BASE_MANY_VALUED_CONNECTIVES),
#         FiniteHeytingAlgebra(G4),
#         timeout=max_timeout
#     )
#     end
# end

############################################################################################
#### H4 ####################################################################################
############################################################################################

using SoleLogics.ManyValuedLogics: H4
using SoleLogics.ManyValuedLogics: α, β
myoperators4 = []
append!(myoperators4, BASE_MANY_VALUED_CONNECTIVES)
append!(myoperators4, getdomain(H4))
opweights4 = [10, 10, 10, 1, 1, 1, 1]

for height in 2:2
    # println("Alphasat on H4 formulas of height up to " * string(height) * "\n")
    # for i in 1:max_it
    #     @test alphasat(
    #     rand(MersenneTwister(i), getdomain(H4)),
    #     randformula(MersenneTwister(i), height, myalphabet, BASE_MANY_VALUED_CONNECTIVES),
    #     H4,
    #     timeout=max_timeout,
    #     # verbose = true
    # ) == alphasat(
    #     rand(MersenneTwister(i), getdomain(H4)),
    #     randformula(MersenneTwister(i), height, myalphabet, BASE_MANY_VALUED_CONNECTIVES),
    #     FiniteHeytingAlgebra(H4),
    #     timeout=max_timeout
    # )
    # end
    println("Alphaprove on H4 formulas of height up to " * string(height) * "\n")
    #for i in max_it-14:max_it-14
    for i in 1:max_it
        @test alphaprove(
        rand(MersenneTwister(i), getdomain(H4)),
        randformula(MersenneTwister(i), height, myalphabet, BASE_MANY_VALUED_CONNECTIVES),
        H4,
        timeout=max_timeout,
        # verbose = true
    ) == alphaprove(
        rand(MersenneTwister(i), getdomain(H4)),
        randformula(MersenneTwister(i), height, myalphabet, BASE_MANY_VALUED_CONNECTIVES),
        FiniteHeytingAlgebra(H4),
        timeout=max_timeout
    )
    end
end

# ############################################################################################
# #### H9 ####################################################################################
# ############################################################################################

# using SoleLogics.ManyValuedLogics: H9
# using SoleLogics.ManyValuedLogics: α, β, γ, δ, ε, ζ, η
# myoperators9 = []
# append!(myoperators9, BASE_MANY_VALUED_CONNECTIVES)
# append!(myoperators9, getdomain(H9))
# opweights4 = [10, 10, 10, 1, 1, 1, 1, 1, 1, 1, 1, 1]

# for height in 1:max_height
#     println("Alphasat on H9 formulas of height up to " * string(height) * "\n")
#     for i in 1:max_it
#         @test alphasat(
#         rand(MersenneTwister(i), getdomain(H9)),
#         randformula(MersenneTwister(i), height, myalphabet, BASE_MANY_VALUED_CONNECTIVES),
#         H9,
#         timeout=max_timeout
#         # verbose = true
#     ) == alphasat(
#         rand(MersenneTwister(i), getdomain(H9)),
#         randformula(MersenneTwister(i), height, myalphabet, BASE_MANY_VALUED_CONNECTIVES),
#         FiniteHeytingAlgebra(H9),
#         timeout=max_timeout
#     )
#     end
#     println("Alphaprove on H9 formulas of height up to " * string(height) * "\n")
#     for i in 1:max_it
#         @test alphaprove(
#         rand(MersenneTwister(i), getdomain(H9)),
#         randformula(MersenneTwister(i), height, myalphabet, BASE_MANY_VALUED_CONNECTIVES),
#         H9,
#         timeout=max_timeout
#         # verbose = true
#     ) == alphaprove(
#         rand(MersenneTwister(i), getdomain(H9)),
#         randformula(MersenneTwister(i), height, myalphabet, BASE_MANY_VALUED_CONNECTIVES),
#         FiniteHeytingAlgebra(H9),
#         timeout=max_timeout
#     )
#     end
# end
