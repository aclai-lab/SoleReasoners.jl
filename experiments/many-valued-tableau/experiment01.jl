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
max_it = 20000
max_avg = 5000
max_timeout = 1 # seconds

############################################################################################
#### BooleanAlgebra ########################################################################
############################################################################################

using SoleLogics.ManyValuedLogics: booleanalgebra
myoperators2 = []
append!(myoperators2, BASE_MANY_VALUED_CONNECTIVES)
append!(myoperators2, getdomain(booleanalgebra))
opweights2 = [10, 10, 10, 1, 1]

for height in 1:max_height
    println("Alphasat on booleanalgebra formulas of height " * string(height))
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

using SoleLogics.ManyValuedLogics: G3
myoperators3 = []
append!(myoperators3, BASE_MANY_VALUED_CONNECTIVES)
append!(myoperators3, getdomain(G3))
opweights3 = [10, 10, 10, 1, 1, 1]

for height in 1:max_height
    println("Alphasat on G3 formulas of height " * string(height))
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

using SoleLogics.ManyValuedLogics: Ł3
myoperators3 = []
append!(myoperators3, BASE_MANY_VALUED_CONNECTIVES)
append!(myoperators3, getdomain(Ł3))
opweights3 = [10, 10, 10, 1, 1, 1]

for height in 1:max_height
    println("Alphasat on Ł3 formulas of height " * string(height))
    timeouts = 0
    j = 0
    for i in 1:max_it
        t = rand(MersenneTwister(i), getdomain(Ł3))
        f = randformula(
            MersenneTwister(i),
            height,
            myalphabet,
            myoperators3,
            opweights=opweights3
        )
        if !isbot(t) && SoleLogics.height(f) == height
            j += 1
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

using SoleLogics.ManyValuedLogics: G4
myoperators4 = []
append!(myoperators4, BASE_MANY_VALUED_CONNECTIVES)
append!(myoperators4, getdomain(G4))
opweights4 = [10, 10, 10, 1, 1, 1, 1]

for height in 1:max_height
    println("Alphasat on G4 formulas of height " * string(height))
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

using SoleLogics.ManyValuedLogics: Ł4
myoperators4 = []
append!(myoperators4, BASE_MANY_VALUED_CONNECTIVES)
append!(myoperators4, getdomain(Ł4))
opweights4 = [10, 10, 10, 1, 1, 1, 1]

for height in 1:max_height
    println("Alphasat on Ł4 formulas of height " * string(height))
    timeouts = 0
    j = 0
    for i in 1:max_it
        t = rand(MersenneTwister(i), getdomain(Ł4))
        f = randformula(
            MersenneTwister(i),
            height,
            myalphabet,
            myoperators4,
            opweights=opweights4
        )
        if !isbot(t) && SoleLogics.height(f) == height
            j += 1
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

using SoleLogics.ManyValuedLogics: H4
myoperators4 = []
append!(myoperators4, BASE_MANY_VALUED_CONNECTIVES)
append!(myoperators4, getdomain(H4))
opweights4 = [10, 10, 10, 1, 1, 1, 1]

for height in 1:max_height
    println("Alphasat on H4 formulas of height " * string(height))
    timeouts = 0
    j = 0
    for i in 1:max_it
        t = rand(MersenneTwister(i), getdomain(H4))
        f = randformula(
            MersenneTwister(i),
            height,
            myalphabet,
            myoperators4,
            opweights=opweights4
        )
        if !isbot(t) && SoleLogics.height(f) == height
            j += 1
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
