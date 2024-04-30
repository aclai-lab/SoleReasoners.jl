using BenchmarkTools
using Random
using SoleLogics
using SoleLogics.ManyValuedLogics
using SoleReasoners
using Test

BASE_MANY_VALUED_CONNECTIVES = [∨, ∧, →]
BaseManyValuedConnectives = Union{typeof.(BASE_MANY_VALUED_CONNECTIVES)...}

myalphabet = Atom.(["p", "q"])

max_height = 4
max_it = 100
max_timeout = 10 # seconds

############################################################################################
#### BooleanAlgebra ########################################################################
############################################################################################

include("algebras/booleanalgebra.jl")
myoperators2 = []
append!(myoperators2, BASE_MANY_VALUED_CONNECTIVES)
append!(myoperators2, d2)
opweights4 = [10, 10, 10, 1, 1]

for height in 1:max_height
    println("Alphasat on booleanalgebra formulas of height up to " * string(height) * "\n")
    for i in 1:max_it
        @test alphasat(
        rand(MersenneTwister(i), d2),
        randformula(MersenneTwister(i), height, myalphabet, BASE_MANY_VALUED_CONNECTIVES),
        booleanalgebra,
        timeout=max_timeout
        # verbose = true
    ) == alphasat(
        rand(MersenneTwister(i), d2),
        randformula(MersenneTwister(i), height, myalphabet, BASE_MANY_VALUED_CONNECTIVES),
        FiniteHeytingAlgebra(booleanalgebra),
        timeout=max_timeout
    )
    end
    println("Alphaprove on booleanalgebra formulas of height up to " * string(height) * "\n")
    for i in 1:max_it
        @test alphaprove(
        rand(MersenneTwister(i), d2),
        randformula(MersenneTwister(i), height, myalphabet, BASE_MANY_VALUED_CONNECTIVES),
        booleanalgebra,
        timeout=max_timeout
        # verbose = true
    ) == alphaprove(
        rand(MersenneTwister(i), d2),
        randformula(MersenneTwister(i), height, myalphabet, BASE_MANY_VALUED_CONNECTIVES),
        FiniteHeytingAlgebra(booleanalgebra),
        timeout=max_timeout
    )
    end
end

############################################################################################
#### G3 ####################################################################################
############################################################################################

include("algebras/g3.jl")
myoperators3 = []
append!(myoperators3, BASE_MANY_VALUED_CONNECTIVES)
append!(myoperators3, d3)
opweights4 = [10, 10, 10, 1, 1, 1]

for height in 1:max_height
    println("Alphasat on G3 formulas of height up to " * string(height) * "\n")
    for i in 1:max_it
        @test alphasat(
        rand(MersenneTwister(i), d3),
        randformula(MersenneTwister(i), height, myalphabet, BASE_MANY_VALUED_CONNECTIVES),
        G3,
        timeout=max_timeout
        # verbose = true
    ) == alphasat(
        rand(MersenneTwister(i), d3),
        randformula(MersenneTwister(i), height, myalphabet, BASE_MANY_VALUED_CONNECTIVES),
        FiniteHeytingAlgebra(G3),
        timeout=max_timeout
    )
    end
    println("Alphaprove on G3 formulas of height up to " * string(height) * "\n")
    for i in 1:max_it
        @test alphaprove(
        rand(MersenneTwister(i), d3),
        randformula(MersenneTwister(i), height, myalphabet, BASE_MANY_VALUED_CONNECTIVES),
        G3,
        timeout=max_timeout
        # verbose = true
    ) == alphaprove(
        rand(MersenneTwister(i), d3),
        randformula(MersenneTwister(i), height, myalphabet, BASE_MANY_VALUED_CONNECTIVES),
        FiniteHeytingAlgebra(G3),
        timeout=max_timeout
    )
    end
end

############################################################################################
#### G4 ####################################################################################
############################################################################################

include("algebras/g4.jl")
myoperators4 = []
append!(myoperators4, BASE_MANY_VALUED_CONNECTIVES)
append!(myoperators4, d4)
opweights4 = [10, 10, 10, 1, 1, 1, 1]

for height in 1:max_height
    println("Alphasat on G4 formulas of height up to " * string(height) * "\n")
    for i in 1:max_it
        @test alphasat(
        rand(MersenneTwister(i), d4),
        randformula(MersenneTwister(i), height, myalphabet, BASE_MANY_VALUED_CONNECTIVES),
        G4,
        timeout=max_timeout
        # verbose = true
    ) == alphasat(
        rand(MersenneTwister(i), d4),
        randformula(MersenneTwister(i), height, myalphabet, BASE_MANY_VALUED_CONNECTIVES),
        FiniteHeytingAlgebra(G4),
        timeout=max_timeout
    )
    end
    println("Alphaprove on G4 formulas of height up to " * string(height) * "\n")
    for i in 1:max_it
        @test alphaprove(
        rand(MersenneTwister(i), d4),
        randformula(MersenneTwister(i), height, myalphabet, BASE_MANY_VALUED_CONNECTIVES),
        G4,
        timeout=max_timeout
        # verbose = true
    ) == alphaprove(
        rand(MersenneTwister(i), d4),
        randformula(MersenneTwister(i), height, myalphabet, BASE_MANY_VALUED_CONNECTIVES),
        FiniteHeytingAlgebra(G4),
        timeout=max_timeout
    )
    end
end

############################################################################################
#### H4 ####################################################################################
############################################################################################

include("algebras/h4.jl")
myoperators4 = []
append!(myoperators4, BASE_MANY_VALUED_CONNECTIVES)
append!(myoperators4, d4)
opweights4 = [10, 10, 10, 1, 1, 1, 1]

for height in 1:max_height
    println("Alphasat on H4 formulas of height up to " * string(height) * "\n")
    for i in 1:max_it
        @test alphasat(
        rand(MersenneTwister(i), d4),
        randformula(MersenneTwister(i), height, myalphabet, BASE_MANY_VALUED_CONNECTIVES),
        H4,
        timeout=max_timeout
        # verbose = true
    ) == alphasat(
        rand(MersenneTwister(i), d4),
        randformula(MersenneTwister(i), height, myalphabet, BASE_MANY_VALUED_CONNECTIVES),
        FiniteHeytingAlgebra(H4),
        timeout=max_timeout
    )
    end
    println("Alphaprove on H4 formulas of height up to " * string(height) * "\n")
    for i in 1:max_it
        @test alphaprove(
        rand(MersenneTwister(i), d4),
        randformula(MersenneTwister(i), height, myalphabet, BASE_MANY_VALUED_CONNECTIVES),
        H4,
        timeout=max_timeout
        # verbose = true
    ) == alphaprove(
        rand(MersenneTwister(i), d4),
        randformula(MersenneTwister(i), height, myalphabet, BASE_MANY_VALUED_CONNECTIVES),
        FiniteHeytingAlgebra(H4),
        timeout=max_timeout
    )
    end
end

############################################################################################
#### H9 ####################################################################################
############################################################################################

include("algebras/h9.jl")
myoperators9 = []
append!(myoperators9, BASE_MANY_VALUED_CONNECTIVES)
append!(myoperators9, d9)
opweights4 = [10, 10, 10, 1, 1, 1, 1, 1, 1, 1, 1, 1]

for height in 1:max_height
    println("Alphasat on H9 formulas of height up to " * string(height) * "\n")
    for i in 1:max_it
        @test alphasat(
        rand(MersenneTwister(i), d4),
        randformula(MersenneTwister(i), height, myalphabet, BASE_MANY_VALUED_CONNECTIVES),
        H9,
        timeout=max_timeout
        # verbose = true
    ) == alphasat(
        rand(MersenneTwister(i), d4),
        randformula(MersenneTwister(i), height, myalphabet, BASE_MANY_VALUED_CONNECTIVES),
        FiniteHeytingAlgebra(H9),
        timeout=max_timeout
    )
    end
    println("Alphaprove on H9 formulas of height up to " * string(height) * "\n")
    for i in 1:max_it
        @test alphaprove(
        rand(MersenneTwister(i), d4),
        randformula(MersenneTwister(i), height, myalphabet, BASE_MANY_VALUED_CONNECTIVES),
        H9,
        timeout=max_timeout
        # verbose = true
    ) == alphaprove(
        rand(MersenneTwister(i), d4),
        randformula(MersenneTwister(i), height, myalphabet, BASE_MANY_VALUED_CONNECTIVES),
        FiniteHeytingAlgebra(H9),
        timeout=max_timeout
    )
    end
end
