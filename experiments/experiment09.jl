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
max_it = 1000
max_avg = 500
max_timeout = 60 # seconds

using SoleLogics.ManyValuedLogics: booleanalgebra
myoperators2 = []
append!(myoperators2, BASE_MANY_VALUED_CONNECTIVES)
append!(myoperators2, getdomain(booleanalgebra))
opweights2 = [10, 10, 10, 1, 1]

using SoleLogics.ManyValuedLogics: G3, Ł3
myoperators3 = []
append!(myoperators3, BASE_MANY_VALUED_CONNECTIVES)
append!(myoperators3, getdomain(G3))
opweights3 = [10, 10, 10, 1, 1, 1]

using SoleLogics.ManyValuedLogics: G4, Ł4, H4
myoperators4 = []
append!(myoperators4, BASE_MANY_VALUED_CONNECTIVES)
append!(myoperators4, getdomain(G4))
opweights4 = [10, 10, 10, 1, 1, 1, 1]

using SoleLogics.ManyValuedLogics: G5
myoperators5 = []
append!(myoperators5, BASE_MANY_VALUED_CONNECTIVES)
append!(myoperators5, getdomain(G5))
opweights5 = [10, 10, 10, 1, 1, 1, 1, 1]

using SoleLogics.ManyValuedLogics: G6, H6_1, H6_2, H6_3, H6
myoperators6 = []
append!(myoperators6, BASE_MANY_VALUED_CONNECTIVES)
append!(myoperators6, getdomain(G6))
opweights6 = [10, 10, 10, 1, 1, 1, 1, 1, 1]

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
    for height in 1:max_height
        println("Alphasat on " * a[1] * " formulas of height " * string(height))
        j = 0
        sat = 0
        unsat = 0
        skipped = 0
        for i in 1:max_it
            f = randformula(
                MersenneTwister(i),
                height,
                myalphabet,
                a[3],
                opweights=a[4]
            )
            if SoleLogics.height(f) == height
                t = rand(MersenneTwister(i), getdomain(a[2]))
                brng = MersenneTwister(i)
                r = alphasat(
                    t,
                    f,
                    a[2],
                    rng=brng,
                    timeout=max_timeout
                )
                if isnothing(r)
                    skipped +=1
                else
                    j += 1
                    if r
                        sat += 1
                    else
                        unsat +=1
                    end
                end
                if j == max_avg
                    break
                end
                if i == max_it
                    @warn "Maximum iterations reached"
                end
            end
        end
        println("$sat/$max_avg formulas returned true, $unsat/$max_avg formulas returned false, $skipped formulas reached timeout\n")
    end
    println()
end

println()
println()

for a in algebras
    for height in 1:max_height
        println("Alphaprove on " * a[1] * " formulas of height " * string(height))
        j = 0
        sat = 0
        unsat = 0
        skipped = 0
        for i in 1:max_it
            f = randformula(
                MersenneTwister(i),
                height,
                myalphabet,
                a[3],
                opweights=a[4]
            )
            if SoleLogics.height(f) == height
                t = rand(MersenneTwister(i), getdomain(a[2]))
                brng = MersenneTwister(i)
                r = alphaprove(
                    t,
                    f,
                    a[2],
                    rng=brng,
                    timeout=max_timeout
                )
                if isnothing(r)
                    skipped += 1
                else
                    j += 1
                    if r
                        sat += 1
                    else
                        unsat +=1
                    end
                end
                if j == max_avg
                    break
                end
                if i == max_it
                    @warn "Maximum iterations reached"
                end
            end
        end
        println("$sat/$max_avg formulas returned true, $unsat/$max_avg formulas returned false, $skipped formulas reached timeout\n")
    end
    println()
end
