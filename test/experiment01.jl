using BenchmarkTools
using Random
using SoleLogics
using SoleLogics.ManyValuedLogics
using SoleReasoners
using Test

BASE_MANY_VALUED_CONNECTIVES = [∨, ∧, →]
BaseManyValuedConnectives = Union{typeof.(BASE_MANY_VALUED_CONNECTIVES)...}

myalphabet = Atom.(["p", "q", "r"])

max_height = 10
max_it = 6000
max_avg = 5000
max_timeout = 1 # seconds

############################################################################################
#### BooleanAlgebra ########################################################################
############################################################################################

include("algebras/booleanalgebra.jl")
myoperators2 = []
append!(myoperators2, BASE_MANY_VALUED_CONNECTIVES)
append!(myoperators2, d2)
opweights2 = [10, 10, 10, 1, 1]

for height in 1:max_height
    println("Alphasat on booleanalgebra formulas of height " * string(height))
    timeouts = 0
    j = 0
    for i in 1:max_it
        f = randformula(
            MersenneTwister(i),
            height,
            myalphabet,
            myoperators2,
            opweights=opweights2
        )
        if SoleLogics.height(f) == height
            j += 1
            t = rand(MersenneTwister(i), d2)
            brng = MersenneTwister(i)
            r = alphasat(
                t,
                f,
                booleanalgebra,
                rng=brng,
                timeout=max_timeout
            )
            if isnothing(r)
                timeouts += 1
            end
            if j == max_avg
                break
            end
            if i == max_it
                println("Warning: maximum iterations reached")
            end
        end
    end
    println(string(timeouts) * " formulas over " * string(max_avg) * " timeout\n")
end
println()

############################################################################################
#### G3 ####################################################################################
############################################################################################

include("algebras/g3.jl")
myoperators3 = []
append!(myoperators3, BASE_MANY_VALUED_CONNECTIVES)
append!(myoperators3, d3)
opweights3 = [10, 10, 10, 1, 1, 1]

for height in 1:max_height
    println("Alphasat on G3 formulas of height " * string(height))
    timeouts = 0
    j = 0
    for i in 1:max_it
        f = randformula(
            MersenneTwister(i),
            height,
            myalphabet,
            myoperators3,
            opweights=opweights3
        )
        if SoleLogics.height(f) == height
            j += 1
            t = rand(MersenneTwister(i), d3)
            brng = MersenneTwister(i)
            r = alphasat(
                t,
                f,
                G3,
                rng=brng,
                timeout=max_timeout
            )
            if isnothing(r)
                timeouts += 1
            end
            if j == max_avg
                break
            end
            if i == max_it
                println("Warning: maximum iterations reached")
            end
        end
    end
    println(string(timeouts) * " formulas over " * string(max_avg) * " timeout\n")
end
println()

############################################################################################
#### Ł3 ####################################################################################
############################################################################################

include("algebras/l3.jl")
myoperators3 = []
append!(myoperators3, BASE_MANY_VALUED_CONNECTIVES)
append!(myoperators3, d3)
opweights3 = [10, 10, 10, 1, 1, 1]

for height in 1:max_height
    println("Alphasat on Ł3 formulas of height " * string(height))
    timeouts = 0
    j = 0
    for i in 1:max_it
        f = randformula(
            MersenneTwister(i),
            height,
            myalphabet,
            myoperators3,
            opweights=opweights3
        )
        if SoleLogics.height(f) == height
            j += 1
            t = rand(MersenneTwister(i), d3)
            brng = MersenneTwister(i)
            r = alphasat(
                t,
                f,
                Ł3,
                rng=brng,
                timeout=max_timeout
            )
            if isnothing(r)
                timeouts += 1
            end
            if j == max_avg
                break
            end
            if i == max_it
                println("Warning: maximum iterations reached")
            end
        end
    end
    println(string(timeouts) * " formulas over " * string(max_avg) * " timeout\n")
end
println()

############################################################################################
#### G4 ####################################################################################
############################################################################################

include("algebras/g4.jl")
myoperators4 = []
append!(myoperators4, BASE_MANY_VALUED_CONNECTIVES)
append!(myoperators4, d4)
opweights4 = [10, 10, 10, 1, 1, 1, 1]

for height in 1:max_height
    println("Alphasat on G4 formulas of height " * string(height))
    timeouts = 0
    j = 0
    for i in 1:max_it
        f = randformula(
            MersenneTwister(i),
            height,
            myalphabet,
            myoperators4,
            opweights=opweights4
        )
        if SoleLogics.height(f) == height
            j += 1
            t = rand(MersenneTwister(i), d4)
            brng = MersenneTwister(i)
            r = alphasat(
                t,
                f,
                G4,
                rng=brng,
                timeout=max_timeout
            )
            if isnothing(r)
                timeouts += 1
            end
            if j == max_avg
                break
            end
            if i == max_it
                println("Warning: maximum iterations reached")
            end
        end
    end
    println(string(timeouts) * " formulas over " * string(max_avg) * " timeout\n")
end
println()

############################################################################################
#### Ł4 ####################################################################################
############################################################################################

include("algebras/l4.jl")
myoperators4 = []
append!(myoperators4, BASE_MANY_VALUED_CONNECTIVES)
append!(myoperators4, d4)
opweights4 = [10, 10, 10, 1, 1, 1, 1]

for height in 1:max_height
    println("Alphasat on Ł4 formulas of height " * string(height))
    timeouts = 0
    j = 0
    for i in 1:max_it
        f = randformula(
            MersenneTwister(i),
            height,
            myalphabet,
            myoperators4,
            opweights=opweights4
        )
        if SoleLogics.height(f) == height
            j += 1
            t = rand(MersenneTwister(i), d4)
            brng = MersenneTwister(i)
            r = alphasat(
                t,
                f,
                Ł4,
                rng=brng,
                timeout=max_timeout
            )
            if isnothing(r)
                timeouts += 1
            end
            if j == max_avg
                break
            end
            if i == max_it
                println("Warning: maximum iterations reached")
            end
        end
    end
    println(string(timeouts) * " formulas over " * string(max_avg) * " timeout\n")
end
println()

############################################################################################
#### H4 ####################################################################################
############################################################################################

include("algebras/h4.jl")
myoperators4 = []
append!(myoperators4, BASE_MANY_VALUED_CONNECTIVES)
append!(myoperators4, d4)
opweights4 = [10, 10, 10, 1, 1, 1, 1]

for height in 1:max_height
    println("Alphasat on H4 formulas of height " * string(height))
    timeouts = 0
    j = 0
    for i in 1:max_it
        f = randformula(
            MersenneTwister(i),
            height,
            myalphabet,
            myoperators4,
            opweights=opweights4
        )
        if SoleLogics.height(f) == height
            j += 1
            t = rand(MersenneTwister(i), d4)
            brng = MersenneTwister(i)
            r = alphasat(
                t,
                f,
                H4,
                rng=brng,
                timeout=max_timeout
            )
            if isnothing(r)
                timeouts += 1
            end
            if j == max_avg
                break
            end
            if i == max_it
                println("Warning: maximum iterations reached")
            end
        end
    end
    println(string(timeouts) * " formulas over " * string(max_avg) * " timeout\n")
end
println()
