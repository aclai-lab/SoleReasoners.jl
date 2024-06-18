using Random
using SoleReasoners
using SoleLogics
using SoleLogics.ManyValuedLogics

BASE_MANY_VALUED_CONNECTIVES = [∨, ∧, →]
BaseManyValuedConnectives = Union{typeof.(BASE_MANY_VALUED_CONNECTIVES)...}

myalphabet = Atom.(["p", "q", "r"])

max_height = 12
max_it = 100000
max_avg = 10000
max_timeout = 1 # seconds

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

algebras = [
    ("BA",   booleanalgebra, myoperators2, opweights2),
    ("G3",   G3,             myoperators3, opweights3),
    ("Ł3",   Ł3,             myoperators3, opweights3),
    ("G4",   G4,             myoperators4, opweights4),
    ("Ł4",   Ł4,             myoperators4, opweights4),
    ("H4",   H4,             myoperators4, opweights4)
]
for a in algebras
    for height in 1:max_height
        println("Alphasat on " * a[1] * " formulas of height " * string(height))
        j = 0
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
                r = alphasat(
                    t,
                    f,
                    a[2],
                    rng=brng,
                    timeout=max_timeout
                )
                if isnothing(r)
                    timeouts += 1
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
        println()
    end
    println()
end
