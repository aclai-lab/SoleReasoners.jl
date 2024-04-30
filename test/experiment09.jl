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

include("algebras/booleanalgebra.jl")
myoperators2 = []
append!(myoperators2, BASE_MANY_VALUED_CONNECTIVES)
append!(myoperators2, d2)
opweights2 = [10, 10, 10, 1, 1]

include("algebras/g3.jl")
include("algebras/l3.jl")
myoperators3 = []
append!(myoperators3, BASE_MANY_VALUED_CONNECTIVES)
append!(myoperators3, d3)
opweights3 = [10, 10, 10, 1, 1, 1]

include("algebras/g4.jl")
include("algebras/l4.jl")
include("algebras/h4.jl")
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
include("algebras/sixvaluedalgebras/h6_1.jl")
include("algebras/sixvaluedalgebras/h6_2.jl")
include("algebras/sixvaluedalgebras/h6_3.jl")
include("algebras/sixvaluedalgebras/h6.jl")
myoperators6 = []
append!(myoperators6, BASE_MANY_VALUED_CONNECTIVES)
append!(myoperators6, d6)
opweights6 = [10, 10, 10, 1, 1, 1, 1, 1, 1]

algebras = [
    ("BA",   booleanalgebra, d2, myoperators2, opweights2),
    ("G3",   G3,             d3, myoperators3, opweights3),
    ("Ł3",   Ł3,             d3, myoperators3, opweights3),
    ("G4",   G4,             d4, myoperators4, opweights4),
    ("Ł4",   Ł4,             d4, myoperators4, opweights4),
    ("H4",   H4,             d4, myoperators4, opweights4),
    ("G5",   G5,             d5, myoperators5, opweights5),
    ("G6",   G6,             d6, myoperators6, opweights6),
    ("H6_1", H6_1,           d6, myoperators6, opweights6),
    ("H6_2", H6_2,           d6, myoperators6, opweights6),
    ("H6_3", H6_3,           d6, myoperators6, opweights6),
    ("H6",   H6,             d6, myoperators6, opweights6)
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
                a[4],
                opweights=a[5]
            )
            if SoleLogics.height(f) == height
                t = rand(MersenneTwister(i), a[3])
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
                a[4],
                opweights=a[5]
            )
            if SoleLogics.height(f) == height
                t = rand(MersenneTwister(i), a[3])
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
