using Random
using SoleLogics
using SoleLogics.ManyValuedLogics
using SoleReasoners
using StatsBase
import SoleBase: initrng
import SoleLogics: sample

BASE_MANY_VALUED_CONNECTIVES = [
    ∨,
    ∧,
    →
]
BaseManyValuedConnectives = Union{typeof.(BASE_MANY_VALUED_CONNECTIVES)...}

myalphabet = Atom.(["p", "q", "r"])

min_height = 10
max_height = 10
max_it = 20000
max_avg = 1000
max_timeout = 10 # seconds

using SoleLogics.ManyValuedLogics: booleanalgebra
myoperators2 = []
append!(myoperators2, BASE_MANY_VALUED_CONNECTIVES)
append!(myoperators2, getdomain(booleanalgebra))
opweights2 = [10, 10, 10, 1, 1]
# opweights2 = StatsBase.uweights(length(myoperators2))

using SoleLogics.ManyValuedLogics: G3, Ł3
myoperators3 = []
append!(myoperators3, BASE_MANY_VALUED_CONNECTIVES)
append!(myoperators3, getdomain(G3))
opweights3 = [10, 10, 10, 1, 1, 1]
# opweights3 = StatsBase.uweights(length(myoperators3))

using SoleLogics.ManyValuedLogics: G4, Ł4, H4
myoperators4 = []
append!(myoperators4, BASE_MANY_VALUED_CONNECTIVES)
append!(myoperators4, getdomain(G4))
opweights4 = [10, 10, 10, 1, 1, 1, 1]
# opweights4 = StatsBase.uweights(length(myoperators4))

using SoleLogics.ManyValuedLogics: G5
myoperators5 = []
append!(myoperators5, BASE_MANY_VALUED_CONNECTIVES)
append!(myoperators5, getdomain(G5))
opweights5 = [10, 10, 10, 1, 1, 1, 1, 1]
# opweights5 = StatsBase.uweights(length(myoperators5))

using SoleLogics.ManyValuedLogics: G6, H6_1, H6_2, H6_3, H6
myoperators6 = []
append!(myoperators6, BASE_MANY_VALUED_CONNECTIVES)
append!(myoperators6, getdomain(G6))
opweights6 = [10, 10, 10, 1, 1, 1, 1, 1, 1]
# opweights6 = StatsBase.uweights(length(myoperators6))

algebras = [
    ("BA",   booleanalgebra, myoperators2, opweights2),
    ("G3",   G3,             myoperators3, opweights3),
    ("Ł3",   Ł3,             myoperators3, opweights3),
    ("G4",   G4,             myoperators4, opweights4),
    ("Ł4",   Ł4,             myoperators4, opweights4),
    ("H4",   H4,             myoperators4, opweights4),
    ("G5",   G5,             myoperators5, opweights5),
    ("G6",   G6,             myoperators6, opweights6),
    ("H6_1", H6_1,           myoperators6, opweights6),
    ("H6_2", H6_2,           myoperators6, opweights6),
    ("H6_3", H6_3,           myoperators6, opweights6),
    ("H6",   H6,             myoperators6, opweights6)
]

for a in algebras
    rng = initrng(Random.GLOBAL_RNG)
    aot = vcat(myalphabet,getdomain(a[2])) # atoms or truths
    aotweights = StatsBase.uweights(length(myalphabet)+length(getdomain(a[2])))
    aotpicker = (rng)->StatsBase.sample(rng, aot, aotweights)

    atomweights = StatsBase.uweights(length(myalphabet))
    truthweights = StatsBase.uweights(length(getdomain(a[2])))
    leafpicker1 = (rng)->SyntaxTree(
        →,
        (StatsBase.sample(rng, myalphabet, atomweights)),
        (StatsBase.sample(rng, getdomain(a[2]), truthweights))
    )

    leafpicker2 = (rng)->SyntaxTree(
        →,
        (StatsBase.sample(rng, getdomain(a[2]), truthweights)),
        (StatsBase.sample(rng, myalphabet, atomweights))
    )
    leafpickers = [leafpicker1, leafpicker2]
    lpweights = StatsBase.uweights(length(leafpickers))
    leafpicker = (rng)->(StatsBase.sample(rng, leafpickers, lpweights))(rng)
    for height in min_height:max_height
        println("MVHS Alphasat on " * a[1] * " formulas of height " * string(height))
        e_time = 0
        j = 0
        sat = 0
        unsat = 0
        timeouts = 0
        for i in 1:max_it
            t = rand(MersenneTwister(i), getdomain(a[2]))
            f = randformula(
                MersenneTwister(i),
                height,
                # height-1,
                myalphabet,
                a[3],
                opweights=a[4],
                # basecase=leafpicker
            )
            if !isbot(t) && SoleLogics.height(f) == height
                j += 1
                brng = MersenneTwister(i)
                t0 = time_ns()
                r = mvhsalphasat(
                    t,
                    f,
                    a[2],
                    rng=brng,
                    timeout=max_timeout
                )
                t1 = time_ns()
                if isnothing(r)
                    timeouts += 1
                else
                    e_time += t1-t0
                    if r
                        sat += 1
                    else
                        unsat +=1
                    end
                end
                if j == max_avg
                    break
                end
            end
            if i == max_it
                println("Warning: maximum iterations reached")
            end
        end
        println(string(timeouts) * " formulas over " * string(max_avg) * " timeout.")
        println("(" * string(max_avg - timeouts) * " didn't.)")
        print("Average execution time (over " * string(max_avg - timeouts) * " formulas): ")
        println(string((e_time/1e6)/(max_avg - timeouts)) * " ms\n")
        println("$sat/$(max_avg - timeouts) formulas were α-sat, " *
                "$unsat/$(max_avg - timeouts) formulas were not α-sat\n")
        println()
    end
    println()
end
