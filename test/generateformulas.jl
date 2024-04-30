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
max_it = 7000
max_avg = 5000
max_timeout = 1 # seconds

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
    ("booleanalgebra", booleanalgebra, d2, myoperators2, opweights2, "twovaluedformulas"),
    ("G3", G3, d3, myoperators3, opweights3, "threevaluedformulas"),
    ("G4", G4, d4, myoperators4, opweights4, "fourvaluedformulas"),
    ("G5", G5, d5, myoperators5, opweights5, "fivevaluedformulas"),
    ("G6", G6, d6, myoperators6, opweights6, "sixvaluedformulas")
]

for a in algebras
    for height in 1:max_height
        # Open file in append mode and then write to it
        file =  open("formulas/" * a[6] * "/height" * string(height) * ".txt","a")
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
                write(file, syntaxstring(f) * "\n");
                j+=1
                if j == max_avg
                    break
                end
                if i == max_it
                    @warn "Maximum iterations reached"
                end
            end
        end
    end
end
