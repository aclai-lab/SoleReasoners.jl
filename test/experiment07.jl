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

include("algebras/booleanalgebra.jl")
myoperators2 = []
append!(myoperators2, BASE_MANY_VALUED_CONNECTIVES)
append!(myoperators2, d2)
opweights2 = [10, 10, 10, 1, 1]

include("algebras/g3.jl")
myoperators3 = []
append!(myoperators3, BASE_MANY_VALUED_CONNECTIVES)
append!(myoperators3, d3)
opweights3 = [10, 10, 10, 1, 1, 1]

include("algebras/g4.jl")
myoperators4 = []
append!(myoperators4, BASE_MANY_VALUED_CONNECTIVES)
append!(myoperators4, d4)
opweights4 = [10, 10, 10, 1, 1, 1, 1]

include("algebras/g5.jl")
myoperators5 = []
append!(myoperators5, BASE_MANY_VALUED_CONNECTIVES)
append!(myoperators5, d5)
opweights5 = [10, 10, 10, 1, 1, 1, 1, 1]

include("algebras/sixvaluedalgebras/g6.jl")
myoperators6 = []
append!(myoperators6, BASE_MANY_VALUED_CONNECTIVES)
append!(myoperators6, d6)
opweights6 = [10, 10, 10, 1, 1, 1, 1, 1, 1]

algebras = [
    ("booleanalgebra", booleanalgebra, d2, myoperators2, opweights2),
    ("G3", G3, d3, myoperators3, opweights3),
    ("G4", G4, d4, myoperators4, opweights4),
    ("G5", G5, d5, myoperators5, opweights5),
    ("G6", G6, d6, myoperators6, opweights6)
]

for a in algebras
    for height in 1:max_height
        println("Alphasat on " * a[1] * " formulas of height " * string(height))
        e_time = 0
        j = 0
        for i in 1:max_it
            f = randformula(
                MersenneTwister(i),
                height,
                myalphabet,
                a[4],
                opweights=a[5]
            )
            if SoleLogics.height(f) == height
                t = rand(MersenneTwister(i), a[3])
                brng = MersenneTwister(i)
                t0 = time_ns()
                r = alphasat(
                    t,
                    f,
                    a[2],
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
end
