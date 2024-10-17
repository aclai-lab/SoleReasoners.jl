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

using SoleLogics.ManyValuedLogics: booleanalgebra, G3, G4, G5, G6

algebras = [
    ("booleanalgebra", booleanalgebra, "twovaluedformulas"),
    ("G3",             G3,             "threevaluedformulas"),
    ("G4",             G4,             "fourvaluedformulas"),
    ("G5",             G5,             "fivevaluedformulas"),
    ("G6",             G6,             "sixvaluedformulas")
]

for a in algebras
    mkdir(a[3])
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

    operatorweights = StatsBase.uweights(length(BASE_MANY_VALUED_CONNECTIVES))
    operatorpicker = (rng)->SyntaxTree(
        StatsBase.sample(rng, BASE_MANY_VALUED_CONNECTIVES, operatorweights),
        StatsBase.sample(rng, aot, aotweights),
        StatsBase.sample(rng, aot, aotweights)
    )

    endpickers = [operatorpicker, leafpicker]
    endweights = StatsBase.uweights(length(endpickers))
    endpicker = (rng)->(StatsBase.sample(rng, endpickers, endweights))(rng)

    for height in min_height:max_height
        # Open file in append mode and then write to it
        file =  open(a[3] * "/height" * string(height) * ".txt","a")
        j = 0
        for i in 1:max_it
            f = randformula(
                MersenneTwister(i),
                height-1,   # height,
                myalphabet,
                BASE_MANY_VALUED_CONNECTIVES,
                opweights=StatsBase.uweights(length(BASE_MANY_VALUED_CONNECTIVES)),
                basecase=endpicker, #basecase=leafpicker,    # basecase=aotpicker
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
