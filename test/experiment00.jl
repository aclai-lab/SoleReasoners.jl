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

include("algebras/booleanalgebra.jl")
myoperators2 = []
append!(myoperators2, BASE_MANY_VALUED_CONNECTIVES)
append!(myoperators2, d2)
opweights2 = [10, 10, 10, 1, 1]

for height in 1:max_height
    println("Generating booleanalgebra formulas of height " * string(height))
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
            if j == max_avg
                println("$(i-max_avg) formulas over $i were too short ")
                break
            end
            if i == max_it
                println("Warning: maximum iterations reached")
            end
        end
    end
end
println()

include("algebras/g3.jl")
myoperators3 = []
append!(myoperators3, BASE_MANY_VALUED_CONNECTIVES)
append!(myoperators3, d3)
opweights3 = [10, 10, 10, 1, 1, 1]

for height in 1:max_height
    println("Generating G3 formulas of height " * string(height))
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
            if j == max_avg
                println("$(i-max_avg) formulas over $i were too short ")
                break
            end
            if i == max_it
                println("Warning: maximum iterations reached")
            end
        end
    end
end
println()

include("algebras/g4.jl")
myoperators4 = []
append!(myoperators4, BASE_MANY_VALUED_CONNECTIVES)
append!(myoperators4, d4)
opweights4 = [10, 10, 10, 1, 1, 1, 1]

for height in 1:max_height
    println("Generating G4 formulas of height " * string(height))
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
            if j == max_avg
                println("$(i-max_avg) formulas over $i were too short ")
                break
            end
            if i == max_it
                println("Warning: maximum iterations reached")
            end
        end
    end
end
println()
