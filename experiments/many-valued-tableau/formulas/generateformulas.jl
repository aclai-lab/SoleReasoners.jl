# Generate all the formulas used in the experiments
using Random
using SoleLogics
using SoleLogics.ManyValuedLogics
using SoleReasoners
using StatsBase
import SoleBase: initrng
import SoleLogics: sample

BASE_MANY_VALUED_CONNECTIVES = [∨, ∧, →]
BaseManyValuedConnectives = Union{typeof.(BASE_MANY_VALUED_CONNECTIVES)...}

myalphabet = Atom.(["p", "q", "r"])

min_height = 1
max_height = 8
max_it = 20000
max_avg = 1000

using SoleLogics.ManyValuedLogics: booleanalgebra
myoperators2 = []
append!(myoperators2, BASE_MANY_VALUED_CONNECTIVES)
# append!(myoperators2, getdomain(booleanalgebra))
opweights2 = StatsBase.uweights(length(myoperators2))

using SoleLogics.ManyValuedLogics: G3
myoperators3 = []
append!(myoperators3, BASE_MANY_VALUED_CONNECTIVES)
# append!(myoperators3, getdomain(G3))
opweights3 = StatsBase.uweights(length(myoperators3))

using SoleLogics.ManyValuedLogics: G4
myoperators4 = []
append!(myoperators4, BASE_MANY_VALUED_CONNECTIVES)
# append!(myoperators4, getdomain(G4))
opweights4 = StatsBase.uweights(length(myoperators4))

using SoleLogics.ManyValuedLogics: G5
myoperators5 = []
append!(myoperators5, BASE_MANY_VALUED_CONNECTIVES)
# append!(myoperators5, getdomain(G5))
opweights5 = StatsBase.uweights(length(myoperators5))

using SoleLogics.ManyValuedLogics: G6
myoperators6 = []
append!(myoperators6, BASE_MANY_VALUED_CONNECTIVES)
# append!(myoperators6, getdomain(G6))
opweights6 = StatsBase.uweights(length(myoperators6))

algebras = [
    ("booleanalgebra", booleanalgebra, myoperators2, opweights2, "twovaluedformulas"),
    ("G3",             G3,             myoperators3, opweights3, "threevaluedformulas"),
    ("G4",             G4,             myoperators4, opweights4, "fourvaluedformulas"),
    ("G5",             G5,             myoperators5, opweights5, "fivevaluedformulas"),
    ("G6",             G6,             myoperators6, opweights6, "sixvaluedformulas")
]

for a in algebras
    mkdir(a[5])
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
        # Open file in append mode and then write to it
        file =  open(a[5] * "/height" * string(height) * ".txt","a")
        j = 0
        for i in 1:max_it
            f = randformula(
                MersenneTwister(i),
                height,
                # height-1,
                myalphabet,
                a[3],
                opweights=a[4],
                basecase=aotpicker,
                # basecase=leafpicker,
                balanced=true
            )
            # if SoleLogics.height(f) == height
                write(file, syntaxstring(f) * "\n");
                j+=1
                if j == max_avg
                    break
                end
                if i == max_it
                    @warn "Maximum iterations reached"
                end
            # end
        end
    end
end
