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

using SoleLogics.ManyValuedLogics: G6, H6_1, H6_2, H6_3, H6
algebras = [("G6", G6), ("H6_1", H6_1), ("H6_2", H6_2), ("H6_3", H6_3), ("H6", H6)]

myoperators6 = []
append!(myoperators6, BASE_MANY_VALUED_CONNECTIVES)
append!(myoperators6, getdomain(G6))
opweights6 = [10, 10, 10, 1, 1, 1, 1, 1, 1]

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
                myoperators6,
                opweights=opweights6
            )
            if SoleLogics.height(f) == height
                t = rand(MersenneTwister(i), getdomain(a[2]))
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
