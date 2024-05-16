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

using SoleLogics.ManyValuedLogics: booleanalgebra
myoperators2 = []
append!(myoperators2, BASE_MANY_VALUED_CONNECTIVES)
append!(myoperators2, getdomain(booleanalgebra))
opweights2 = [10, 10, 10, 1, 1]

for height in 1:max_height
    println("Generating booleanalgebra formulas of height " * string(height))
    timeouts = 0
    j = 0
    for i in 1:max_it
        t = rand(MersenneTwister(i), getdomain(booleanalgebra))
        f = randformula(
            MersenneTwister(i),
            height,
            myalphabet,
            myoperators2,
            opweights=opweights2
        )
        if !isbot(t) && SoleLogics.height(f) == height
            j += 1
            if j == max_avg
                println("$(i-max_avg) formulas over $i were too short or were tautologies")
                break
            end
            if i == max_it
                println("Warning: maximum iterations reached")
            end
        end
    end
end
println()

using SoleLogics.ManyValuedLogics: G3
myoperators3 = []
append!(myoperators3, BASE_MANY_VALUED_CONNECTIVES)
append!(myoperators3, getdomain(G3))
opweights3 = [10, 10, 10, 1, 1, 1]

for height in 1:max_height
    println("Generating G3 formulas of height " * string(height))
    timeouts = 0
    j = 0
    for i in 1:max_it
        t = rand(MersenneTwister(i), getdomain(G3))
        f = randformula(
            MersenneTwister(i),
            height,
            myalphabet,
            myoperators3,
            opweights=opweights3
        )
        if !isbot(t) && SoleLogics.height(f) == height
            j += 1
            if j == max_avg
                println("$(i-max_avg) formulas over $i were too short or were tautologies")
                break
            end
            if i == max_it
                println("Warning: maximum iterations reached")
            end
        end
    end
end
println()

using SoleLogics.ManyValuedLogics: G4
myoperators4 = []
append!(myoperators4, BASE_MANY_VALUED_CONNECTIVES)
append!(myoperators4, getdomain(G4))
opweights4 = [10, 10, 10, 1, 1, 1, 1]

for height in 1:max_height
    println("Generating G4 formulas of height " * string(height))
    timeouts = 0
    j = 0
    for i in 1:max_it
        t = rand(MersenneTwister(i), getdomain(G4))
        f = randformula(
            MersenneTwister(i),
            height,
            myalphabet,
            myoperators4,
            opweights=opweights4
        )
        if !isbot(t) && SoleLogics.height(f) == height
            j += 1
            if j == max_avg
                println("$(i-max_avg) formulas over $i were too short or were tautologies")
                break
            end
            if i == max_it
                println("Warning: maximum iterations reached")
            end
        end
    end
end
println()

using SoleLogics.ManyValuedLogics: G5
myoperators5 = []
append!(myoperators5, BASE_MANY_VALUED_CONNECTIVES)
append!(myoperators5, getdomain(G5))
opweights5 = [10, 10, 10, 1, 1, 1, 1, 1]

for height in 1:max_height
    println("Generating G5 formulas of height " * string(height))
    timeouts = 0
    j = 0
    for i in 1:max_it
        t = rand(MersenneTwister(i), getdomain(G5))
        f = randformula(
            MersenneTwister(i),
            height,
            myalphabet,
            myoperators5,
            opweights=opweights5
        )
        if !isbot(t) && SoleLogics.height(f) == height
            j += 1
            if j == max_avg
                println("$(i-max_avg) formulas over $i were too short or were tautologies")
                break
            end
            if i == max_it
                println("Warning: maximum iterations reached")
            end
        end
    end
end
println()

using SoleLogics.ManyValuedLogics: G6
myoperators6 = []
append!(myoperators6, BASE_MANY_VALUED_CONNECTIVES)
append!(myoperators6, getdomain(G6))
opweights6 = [10, 10, 10, 1, 1, 1, 1, 1, 1]

for height in 1:max_height
    println("Generating G6 formulas of height " * string(height))
    timeouts = 0
    j = 0
    for i in 1:max_it
        t = rand(MersenneTwister(i), getdomain(G6))
        f = randformula(
            MersenneTwister(i),
            height,
            myalphabet,
            myoperators6,
            opweights=opweights6
        )
        if !isbot(t) && SoleLogics.height(f) == height
            j += 1
            if j == max_avg
                println("$(i-max_avg) formulas over $i were too short or were tautologies")
                break
            end
            if i == max_it
                println("Warning: maximum iterations reached")
            end
        end
    end
end
println()
