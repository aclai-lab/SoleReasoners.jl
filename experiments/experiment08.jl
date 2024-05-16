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

using SoleLogics.ManyValuedLogics: booleanalgebra
myoperators2 = []
append!(myoperators2, BASE_MANY_VALUED_CONNECTIVES)
append!(myoperators2, getdomain(booleanalgebra))
opweights2 = [10, 10, 10, 1, 1]

using SoleLogics.ManyValuedLogics: G3
myoperators3 = []
append!(myoperators3, BASE_MANY_VALUED_CONNECTIVES)
append!(myoperators3, getdomain(G3))
opweights3 = [10, 10, 10, 1, 1, 1]

using SoleLogics.ManyValuedLogics: G4
myoperators4 = []
append!(myoperators4, BASE_MANY_VALUED_CONNECTIVES)
append!(myoperators4, getdomain(G4))
opweights4 = [10, 10, 10, 1, 1, 1, 1]

using SoleLogics.ManyValuedLogics: G5
myoperators5 = []
append!(myoperators5, BASE_MANY_VALUED_CONNECTIVES)
append!(myoperators5, getdomain(G5))
opweights5 = [10, 10, 10, 1, 1, 1, 1, 1]

using SoleLogics.ManyValuedLogics: G6
myoperators6 = []
append!(myoperators6, BASE_MANY_VALUED_CONNECTIVES)
append!(myoperators6, getdomain(G6))
opweights6 = [10, 10, 10, 1, 1, 1, 1, 1, 1]

algebras = [
    ("booleanalgebra", booleanalgebra, myoperators2, opweights2),
    ("G3",             G3,             myoperators3, opweights3),
    ("G4",             G4,             myoperators4, opweights4),
    ("G5",             G5,             myoperators5, opweights5),
    ("G6",             G6,             myoperators6, opweights6)
]

for a in algebras
    for height in 1:max_height
        println("Alphaprove on " * a[1] * " formulas of height " * string(height))
        e_time = 0
        j = 0
        for i in 1:max_it
            t = rand(MersenneTwister(i), getdomain(a[2]))
            f = randformula(
                MersenneTwister(i),
                height,
                myalphabet,
                a[3],
                opweights=a[4]
            )
            if !isbot(t) && SoleLogics.height(f) == height
                brng = MersenneTwister(i)
                t0 = time_ns()
                r = alphaprove(
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
