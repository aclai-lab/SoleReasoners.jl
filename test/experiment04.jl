using BenchmarkTools
using Random
using SoleLogics
using SoleLogics.ManyValuedLogics
using SoleReasoners
using Test

BASE_MANY_VALUED_CONNECTIVES = [∨, ∧, →]
BaseManyValuedConnectives = Union{typeof.(BASE_MANY_VALUED_CONNECTIVES)...}

myalphabet = Atom.(["p", "q", "r"])

max_height = 7
max_it = 500
max_avg = 200
max_timeout = 60 # seconds

############################################################################################
#### BooleanAlgebra ########################################################################
############################################################################################

include("algebras/booleanalgebra.jl")
myoperators2 = []
append!(myoperators2, BASE_MANY_VALUED_CONNECTIVES)
append!(myoperators2, d2)
opweights2 = [10, 10, 10, 1, 1]

for height in 1:max_height
    println("Alphaprove on booleanalgebra formulas of height " * string(height))
    e_time = 0
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
            t = rand(MersenneTwister(i), d2)
            brng = MersenneTwister(i)
            t0 = time_ns()
            r = alphaprove(
                t,
                f,
                booleanalgebra,
                rng=brng,
                timeout=max_timeout
            )
            t1 = time_ns()
            if !isnothing(r)
                j += 1
                e_time += t1-t0
            end
            if j == max_avg
                break
            end
            if i == max_it
                @warn "Maximum iterations reached"
            end
        end
    end
    print("Average execution time (over " * string(max_avg) * " formulas): ")
    println(string((e_time/1e6)/max_avg) * " ms\n")
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
    println("Alphaprove on G3 formulas of height " * string(height))
    e_time = 0
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
            t = rand(MersenneTwister(i), d3)
            brng = MersenneTwister(i)
            t0 = time_ns()
            r = alphaprove(
                t,
                f,
                G3,
                rng=brng,
                timeout=max_timeout
            )
            t1 = time_ns()
            if !isnothing(r)
                j += 1
                e_time += t1-t0
            end
            if j == max_avg
                break
            end
            if i == max_it
                @warn "Maximum iterations reached"
            end
        end
    end
    print("Average execution time (over " * string(max_avg) * " formulas): ")
    println(string((e_time/1e6)/max_avg) * " ms\n")
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
    println("Alphaprove on Ł3 formulas of height " * string(height))
    e_time = 0
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
            t = rand(MersenneTwister(i), d3)
            brng = MersenneTwister(i)
            t0 = time_ns()
            r = alphaprove(
                t,
                f,
                Ł3,
                rng=brng,
                timeout=max_timeout
            )
            t1 = time_ns()
            if !isnothing(r)
                j += 1
                e_time += t1-t0
            end
            if j == max_avg
                break
            end
            if i == max_it
                @warn "Maximum iterations reached"
            end
        end
    end
    print("Average execution time (over " * string(max_avg) * " formulas): ")
    println(string((e_time/1e6)/max_avg) * " ms\n")
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
    println("Alphaprove on G4 formulas of height " * string(height))
    e_time = 0
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
            t = rand(MersenneTwister(i), d4)
            brng = MersenneTwister(i)
            t0 = time_ns()
            r = alphaprove(
                t,
                f,
                G4,
                rng=brng,
                timeout=max_timeout
            )
            t1 = time_ns()
            if !isnothing(r)
                j += 1
                e_time += t1-t0
            end
            if j == max_avg
                break
            end
            if i == max_it
                @warn "Maximum iterations reached"
            end
        end
    end
    print("Average execution time (over " * string(max_avg) * " formulas): ")
    println(string((e_time/1e6)/max_avg) * " ms\n")
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
    println("Alphaprove on Ł4 formulas of height " * string(height))
    e_time = 0
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
            t = rand(MersenneTwister(i), d4)
            brng = MersenneTwister(i)
            t0 = time_ns()
            r = alphaprove(
                t,
                f,
                Ł4,
                rng=brng,
                timeout=max_timeout
            )
            t1 = time_ns()
            if !isnothing(r)
                j += 1
                e_time += t1-t0
            end
            if j == max_avg
                break
            end
            if i == max_it
                @warn "Maximum iterations reached"
            end
        end
    end
    print("Average execution time (over " * string(max_avg) * " formulas): ")
    println(string((e_time/1e6)/max_avg) * " ms\n")
end
println()

# ############################################################################################
# #### H4 ####################################################################################
# ############################################################################################

include("algebras/h4.jl")
myoperators4 = []
append!(myoperators4, BASE_MANY_VALUED_CONNECTIVES)
append!(myoperators4, d4)
opweights4 = [10, 10, 10, 1, 1, 1, 1]

for height in 1:max_height
    println("Alphaprove on H4 formulas of height " * string(height))
    e_time = 0
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
            t = rand(MersenneTwister(i), d4)
            brng = MersenneTwister(i)
            t0 = time_ns()
            r = alphaprove(
                t,
                f,
                H4,
                rng=brng,
                timeout=max_timeout
            )
            t1 = time_ns()
            if !isnothing(r)
                j += 1
                e_time += t1-t0
            end
            if j == max_avg
                break
            end
            if i == max_it
                @warn "Maximum iterations reached"
            end
        end
    end
    print("Average execution time (over " * string(max_avg) * " formulas): ")
    println(string((e_time/1e6)/max_avg) * " ms\n")
end
