using Random
using SoleReasoners
using SoleLogics
using SoleLogics.ManyValuedLogics
using SoleLogics: IA_O # momentary fix
using SoleLogics.ManyValuedLogics: FiniteIndexFLewAlgebra, FiniteIndexTruth

getidxformula(φ::Atom) = φ
getidxformula(φ::T) where {T<:Truth} = convert(FiniteIndexTruth, φ)
function getidxformula(φ::SyntaxBranch)
    if token(φ) isa BoxRelationalConnective || token(φ) isa DiamondRelationalConnective
        token(φ)(getidxformula(SoleLogics.children(φ)[1]))
    else
        token(φ)(getidxformula(SoleLogics.children(φ)[1]), getidxformula(SoleLogics.children(φ)[2]))
    end
end

#################################################################################
min_height = 2
max_height = 3 # 5
max_it = 999
max_avg = 100
max_timeout = 30 # seconds
#################################################################################

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

using SoleLogics.ManyValuedLogics: booleanalgebra
myoperators2 = []
append!(myoperators2, BASE_MANY_VALUED_MODAL_CONNECTIVES)
append!(myoperators2, getdomain(booleanalgebra))
opweights2 = [8, 8, 8, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]

using SoleLogics.ManyValuedLogics: G3, Ł3
myoperators3 = []
append!(myoperators3, BASE_MANY_VALUED_MODAL_CONNECTIVES)
append!(myoperators3, getdomain(G3))
opweights3 = [8, 8, 8, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]

using SoleLogics.ManyValuedLogics: G4, Ł4, H4
myoperators4 = []
append!(myoperators4, BASE_MANY_VALUED_MODAL_CONNECTIVES)
append!(myoperators4, getdomain(G4))
opweights4 = [8, 8, 8, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]

using SoleLogics.ManyValuedLogics: G5
myoperators5 = []
append!(myoperators5, BASE_MANY_VALUED_MODAL_CONNECTIVES)
append!(myoperators5, getdomain(G5))
opweights5 = [8, 8, 8, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]

using SoleLogics.ManyValuedLogics: G6, H6_1, H6_2, H6_3, H6
myoperators6 = []
append!(myoperators6, BASE_MANY_VALUED_MODAL_CONNECTIVES)
append!(myoperators6, getdomain(G6))
opweights6 = [8, 8, 8, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]

algebras = [
    ("BA",   booleanalgebra,    convert(FiniteIndexFLewAlgebra, booleanalgebra), myoperators2, opweights2),
    # ("G3",   G3,                convert(FiniteIndexFLewAlgebra, G3),             myoperators3, opweights3),
    # ("Ł3",   Ł3,                convert(FiniteIndexFLewAlgebra, Ł3),             myoperators3, opweights3),
    # ("G4",   G4,                convert(FiniteIndexFLewAlgebra, G4),             myoperators4, opweights4),
    # ("Ł4",   Ł4,                convert(FiniteIndexFLewAlgebra, Ł4),             myoperators4, opweights4),
    # ("H4",   H4,                convert(FiniteIndexFLewAlgebra, H4),             myoperators4, opweights4),
    # ("G5",   G5,                convert(FiniteIndexFLewAlgebra, G5),             myoperators5, opweights5),
    # ("G6",   G6,                convert(FiniteIndexFLewAlgebra, G6),             myoperators6, opweights6),
    # ("H6_1", H6_1,              convert(FiniteIndexFLewAlgebra, H6_1),           myoperators6, opweights6),
    # ("H6_2", H6_2,              convert(FiniteIndexFLewAlgebra, H6_2),           myoperators6, opweights6),
    # ("H6_3", H6_3,              convert(FiniteIndexFLewAlgebra, H6_3),           myoperators6, opweights6),
    # ("H6",   H6,                convert(FiniteIndexFLewAlgebra, H6),             myoperators6, opweights6)
]

for a in algebras
    for height in min_height:max_height
        println("MVHS Alphaprove on " * a[1] * " formulas of height " * string(height))
        e_time = 0
        hybrid_e_time = 0
        j = 0
        val = 0
        hybrid_val = 0
        unval = 0
        hybrid_unval = 0
        timeouts = 0
        hybrid_timeouts = 0
        for i in 1:max_it
            t = rand(MersenneTwister(i), getdomain(a[2]))
            f = randformula(
                MersenneTwister(i),
                height,
                myalphabet,
                a[4],
                opweights=a[5]
            )
            println("$t ⪯ $f")
            if !isbot(t) && SoleLogics.height(f) == height
                j += 1
                brng = MersenneTwister(i)
                t0 = time_ns()
                r = mvhsalphaprove(
                    t,
                    f,
                    a[2],
                    rng=brng,
                    timeout=max_timeout
                )
                t1 = time_ns()
                hybrid_r = hybridmvhsalphaprove(
                    convert(FiniteIndexTruth, t),
                    getidxformula(f),
                    a[3],
                    rng=brng,
                    timeout=max_timeout
                )
                t2 = time_ns()
                if !isnothing(r) && !isnothing(hybrid_r)
                    @test r == hybrid_r
                end
                if isnothing(r)
                    timeouts += 1
                else
                    e_time += t1-t0
                    if r
                        val += 1
                    else
                        unval +=1
                    end
                end
                if isnothing(hybrid_r)
                    hybrid_timeouts += 1
                else
                    hybrid_e_time += t2-t1
                    if hybrid_r
                        hybrid_val += 1
                    else
                        hybrid_unval +=1
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
        println("Classic MVHS tableau")
        println(string(timeouts) * " formulas over " * string(max_avg) * " timeout.")
        println("(" * string(max_avg - timeouts) * " didn't.)")
        print("Average execution time (over " * string(max_avg - timeouts) * " formulas): ")
        println(string((e_time/1e6)/(max_avg - timeouts)) * " ms\n")
        println("$val/$(max_avg - timeouts) formulas were α-val, " *
                "$unval/$(max_avg - timeouts) formulas were not α-val\n")
        println()
        println("Hybrid MVHS tableau")
        println(string(hybrid_timeouts) * " formulas over " * string(max_avg) * " timeout.")
        println("(" * string(max_avg - hybrid_timeouts) * " didn't.)")
        print("Average execution time (over " * string(max_avg - hybrid_timeouts) * " formulas): ")
        println(string((hybrid_e_time/1e6)/(max_avg - hybrid_timeouts)) * " ms\n")
        println("$hybrid_val/$(max_avg - hybrid_timeouts) formulas were α-val, " *
                "$hybrid_unval/$(max_avg - hybrid_timeouts) formulas were not α-val\n")
        println()
    end
    println()
end
