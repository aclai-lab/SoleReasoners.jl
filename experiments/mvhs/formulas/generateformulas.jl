# Generate all the formulas used in the experiments
using BenchmarkTools
using Random
using SoleLogics
using SoleLogics.ManyValuedLogics
using SoleReasoners
using Test

using SoleLogics: IA_O # momentary fix

diamondA = diamond(IA_A)
diamondL = diamond(IA_L)
diamondB = diamond(IA_B)
diamondE = diamond(IA_E)
diamondD = diamond(IA_D)
diamondO = diamond(IA_O)
diamondAi = diamond(IA_Ai)
diamondLi = diamond(IA_Li)
diamondBi = diamond(IA_Bi)
diamondEi = diamond(IA_Ei)
diamondDi = diamond(IA_Di)
diamondOi = diamond(IA_Oi)
boxA = box(IA_A)
boxL = box(IA_L)
boxB = box(IA_B)
boxE = box(IA_E)
boxD = box(IA_D)
boxO = box(IA_O)
boxAi = box(IA_Ai)
boxLi = box(IA_Li)
boxBi = box(IA_Bi)
boxEi = box(IA_Ei)
boxDi = box(IA_Di)
boxOi = box(IA_Oi)

BASE_MANY_VALUED_MODAL_CONNECTIVES = [
    ∨,
    ∧,
    →,
    diamondA,
    diamondL,
    diamondB,
    diamondE,
    diamondD,
    diamondO,
    diamondAi,
    diamondLi,
    diamondBi,
    diamondEi,
    diamondDi,
    diamondOi,
]
BaseManyValuedConnectives = Union{typeof.(BASE_MANY_VALUED_MODAL_CONNECTIVES)...}

myalphabet = Atom.(["p", "q"])

myalphabet = Atom.(["p", "q", "r"])

BASE_MANY_VALUED_MODAL_CONNECTIVES = [
    ∨,
    ∧,
    →,
    diamondA,
    diamondL,
    diamondB,
    diamondE,
    diamondD,
    diamondO,
    diamondAi,
    diamondLi,
    diamondBi,
    diamondEi,
    diamondDi,
    diamondOi,
    boxA,
    boxL,
    boxB,
    boxE,
    boxD,
    boxO,
    boxAi,
    boxLi,
    boxBi,
    boxEi,
    boxDi,
    boxOi
]
BaseManyValuedConnectives = Union{typeof.(BASE_MANY_VALUED_MODAL_CONNECTIVES)...}

myalphabet = Atom.(["p", "q", "r"])

min_height = 1
max_height = 5
max_it = 999
max_avg = 100

using SoleLogics.ManyValuedLogics: booleanalgebra
myoperators2 = []
append!(myoperators2, BASE_MANY_VALUED_MODAL_CONNECTIVES)
append!(myoperators2, getdomain(booleanalgebra))
opweights2 = [8, 8, 8, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]

using SoleLogics.ManyValuedLogics: G3
myoperators3 = []
append!(myoperators3, BASE_MANY_VALUED_MODAL_CONNECTIVES)
append!(myoperators3, getdomain(G3))
opweights3 = [8, 8, 8, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]

using SoleLogics.ManyValuedLogics: G4
myoperators4 = []
append!(myoperators4, BASE_MANY_VALUED_MODAL_CONNECTIVES)
append!(myoperators4, getdomain(G4))
opweights4 = [8, 8, 8, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]

using SoleLogics.ManyValuedLogics: G5
myoperators5 = []
append!(myoperators5, BASE_MANY_VALUED_MODAL_CONNECTIVES)
append!(myoperators5, getdomain(G5))
opweights5 = [8, 8, 8, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]

using SoleLogics.ManyValuedLogics: G6
myoperators6 = []
append!(myoperators6, BASE_MANY_VALUED_MODAL_CONNECTIVES)
append!(myoperators6, getdomain(G6))
opweights6 = [8, 8, 8, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]

algebras = [
    ("BA",   booleanalgebra, myoperators2, opweights2, "twovaluedformulas"),
    ("G3",   G3,             myoperators3, opweights3, "threevaluedformulas"),
    ("G4",   G4,             myoperators4, opweights4, "fourvaluedformulas"),
    ("G5",   G5,             myoperators5, opweights5, "fivevaluedformulas"),
    ("G6",   G6,             myoperators6, opweights6, "sixvaluedformulas")
]

for a in algebras
    mkdir(a[5])
    for height in min_height:max_height
        # Open file in append mode and then write to it
        file =  open(a[5] * "/height" * string(height) * ".txt","a")
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
                write(file, "($t⪯$(syntaxstring(f)))\n");
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
