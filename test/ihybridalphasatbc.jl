using Random
using SoleLogics
using SoleLogics.ManyValuedLogics
using SoleReasoners
using StatsBase
import SoleBase: initrng
import SoleLogics: sample

getidxformula(φ::Atom) = φ
getidxformula(φ::T) where {T<:Truth} = convert(FiniteIndexTruth, φ)
getidxformula(φ::SyntaxBranch) = token(φ)(getidxformula(SoleLogics.children(φ)[1]), getidxformula(SoleLogics.children(φ)[2]))

BASE_MANY_VALUED_CONNECTIVES = [
    ∨,
    ∧,
    →
]
BaseManyValuedConnectives = Union{typeof.(BASE_MANY_VALUED_CONNECTIVES)...}

myalphabet = Atom.(["p", "q", "r"])

min_height = 1
max_height = 8
max_it = 20000
max_avg = 100
max_timeout = 10 # seconds

using SoleLogics.ManyValuedLogics: booleanalgebra, G3, Ł3, G4, Ł4, H4
using SoleLogics.ManyValuedLogics: G5, G6, H6_1, H6_2, H6_3, H6
using SoleLogics.ManyValuedLogics: FiniteIndexFLewAlgebra, FiniteIndexTruth

algebras = [
    ("BA",   booleanalgebra, convert(FiniteIndexFLewAlgebra, booleanalgebra)),
    ("G3",   G3, convert(FiniteIndexFLewAlgebra, G3)),
    # ("Ł3",   Ł3, convert(FiniteIndexFLewAlgebra, Ł3)),
    # ("G4",   G4, convert(FiniteIndexFLewAlgebra, G4)),
    # ("Ł4",   Ł4, convert(FiniteIndexFLewAlgebra, Ł4)),
    # ("H4",   H4, convert(FiniteIndexFLewAlgebra, H4)),
    # ("G5",   G5, convert(FiniteIndexFLewAlgebra, G5)),
    # ("G6",   G6, convert(FiniteIndexFLewAlgebra, G6)),
    # ("H6_1", H6_1, convert(FiniteIndexFLewAlgebra, H6_1)),
    # ("H6_2", H6_2, convert(FiniteIndexFLewAlgebra, H6_2)),
    # ("H6_3", H6_3, convert(FiniteIndexFLewAlgebra, H6_3)),
    ("H6",   H6, convert(FiniteIndexFLewAlgebra, H6))
]

for a in algebras

    # Formula generation
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
        j = 0
        for i in 1:max_it
            t = rand(MersenneTwister(i), getdomain(a[2]))
            f = randformula(
                MersenneTwister(i),
                height-1,   # height,
                myalphabet,
                BASE_MANY_VALUED_CONNECTIVES,
                opweights=StatsBase.uweights(length(BASE_MANY_VALUED_CONNECTIVES)),
                basecase=leafpicker,    # basecase=aotpicker
                balanced=true
            )
            f1 = getidxformula(f)
            if !isbot(t) && SoleLogics.height(f) == height
                j += 1
                brng = MersenneTwister(i)

                t0 = time_ns()
                r = alphasat(
                    t,
                    f,
                    a[2],
                    rng=brng,
                    timeout=max_timeout
                )
                r_hybrid = hybridalphasat(
                    convert(FiniteIndexTruth, t),
                    f1,
                    a[3],
                    rng=brng,
                    timeout=max_timeout
                )
                if !isnothing(r) && !isnothing(r_hybrid) 
                    @test r == r_hybrid
                end
                if j == max_avg
                    break
                end
            end
            if i == max_it
                @warn "Warning: maximum iterations reached"
            end
        end
    end
end