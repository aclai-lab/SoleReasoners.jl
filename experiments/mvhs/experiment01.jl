using Random
using SoleReasoners
using SoleLogics
using SoleLogics.ManyValuedLogics

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

min_height = 1
max_height = 3
max_it = 20
max_avg = 5
max_timeout = 10 # seconds

using SoleLogics.ManyValuedLogics: booleanalgebra
myoperators2 = []
append!(myoperators2, BASE_MANY_VALUED_MODAL_CONNECTIVES)
append!(myoperators2, getdomain(booleanalgebra))
opweights2 = [4, 4, 4, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]

using SoleLogics.ManyValuedLogics: G3, Ł3
myoperators3 = []
append!(myoperators3, BASE_MANY_VALUED_MODAL_CONNECTIVES)
append!(myoperators3, getdomain(G3))
opweights3 = [4, 4, 4, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]

using SoleLogics.ManyValuedLogics: G4, Ł4, H4
myoperators4 = []
append!(myoperators4, BASE_MANY_VALUED_MODAL_CONNECTIVES)
append!(myoperators4, getdomain(G4))
opweights4 = [4, 4, 4, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]

using SoleLogics.ManyValuedLogics: G5
myoperators5 = []
append!(myoperators5, BASE_MANY_VALUED_MODAL_CONNECTIVES)
append!(myoperators5, getdomain(G5))
opweights5 = [4, 4, 4, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]

using SoleLogics.ManyValuedLogics: G6, H6_1, H6_2, H6_3, H6
myoperators6 = []
append!(myoperators6, BASE_MANY_VALUED_MODAL_CONNECTIVES)
append!(myoperators6, getdomain(G6))
opweights6 = [4, 4, 4, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]

algebras = [
    ("BA",   booleanalgebra, myoperators2, opweights2),
    ("G3",   G3,             myoperators3, opweights3),
    # ("Ł3",   Ł3,             myoperators3, opweights3),
    ("G4",   G4,             myoperators4, opweights4),
    # ("Ł4",   Ł4,             myoperators4, opweights4),
    ("H4",   H4,             myoperators4, opweights4),
    ("G5",   G5,             myoperators5, opweights5),
    ("G6",   G6,             myoperators6, opweights6),
    # ("H6_1", H6_1,           myoperators6, opweights6),
    # ("H6_2", H6_2,           myoperators6, opweights6),
    # ("H6_3", H6_3,           myoperators6, opweights6),
    ("H6",   H6,             myoperators6, opweights6)
]

for a in algebras
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
                myalphabet,
                a[3],
                opweights=a[4]
            )
            if !isbot(t) && SoleLogics.height(f) == height
                j += 1
                brng = MersenneTwister(i)
                t0 = time_ns()
                r = mvhsalphasat(
                    convert(FiniteTruth,t),
                    f,
                    FiniteHeytingAlgebra(a[2]),
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
