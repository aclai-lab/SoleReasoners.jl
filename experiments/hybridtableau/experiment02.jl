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
max_avg = 1000
max_timeout = 10 # seconds
verbose = true

using SoleLogics.ManyValuedLogics: booleanalgebra, G3, Ł3, G4, Ł4, H4
using SoleLogics.ManyValuedLogics: G5, G6, H6_1, H6_2, H6_3, H6
using SoleLogics.ManyValuedLogics: FiniteIndexFLewAlgebra, FiniteIndexTruth

algebras = [
    ("BA",   booleanalgebra, convert(FiniteIndexFLewAlgebra, booleanalgebra)),
    ("G3",   G3, convert(FiniteIndexFLewAlgebra, G3)),
    ("Ł3",   Ł3, convert(FiniteIndexFLewAlgebra, Ł3)),
    ("G4",   G4, convert(FiniteIndexFLewAlgebra, G4)),
    ("Ł4",   Ł4, convert(FiniteIndexFLewAlgebra, Ł4)),
    ("H4",   H4, convert(FiniteIndexFLewAlgebra, H4)),
    ("G5",   G5, convert(FiniteIndexFLewAlgebra, G5)),
    ("G6",   G6, convert(FiniteIndexFLewAlgebra, G6)),
    ("H6_1", H6_1, convert(FiniteIndexFLewAlgebra, H6_1)),
    ("H6_2", H6_2, convert(FiniteIndexFLewAlgebra, H6_2)),
    ("H6_3", H6_3, convert(FiniteIndexFLewAlgebra, H6_3)),
    ("H6",   H6, convert(FiniteIndexFLewAlgebra, H6))
]

# Latex
tot_timeouts = zeros(Int64, length(algebras))   # tot timeouts_classic for each algebra
tot_val = zeros(Int64, length(algebras))        # tot val for each algebra
tot_unval = zeros(Int64, length(algebras))      # tot unval for each algebra

tot_timeouts_hybrid = zeros(Int64, length(algebras))   # tot timeouts_classic for each algebra
tot_val_hybrid = zeros(Int64, length(algebras))        # tot val for each algebra
tot_unval_hybrid = zeros(Int64, length(algebras))      # tot unval for each algebra

for a in algebras
    # Latex
    ntos = zeros(Int64, max_height-min_height+1)   # not timeout for each height    
    ntos_hybrid = zeros(Int64, max_height-min_height+1)   # not timeout for each height    

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
        verbose && println("alphaprove on " * a[1] * " formulas of height " * string(height))

        e_time = 0
        val = 0
        unval = 0
        timeouts_classic = 0

        e_time_hybrid = 0
        val_hybrid = 0
        unval_hybrid = 0
        timeouts_hybrid = 0

        timeouts = 0

        j = 0
        for i in 1:max_it
            t = rand(MersenneTwister(i), getdomain(a[2]))
            t_hybrid = convert(FiniteIndexTruth, t)
            f = randformula(
                MersenneTwister(i),
                height-1,   # height,
                myalphabet,
                BASE_MANY_VALUED_CONNECTIVES,
                opweights=StatsBase.uweights(length(BASE_MANY_VALUED_CONNECTIVES)),
                basecase=leafpicker,    # basecase=aotpicker
                balanced=true
            )
            f_hybrid = getidxformula(f)

            if !isbot(t) && SoleLogics.height(f) == height
                j += 1
                brng = MersenneTwister(i)

                t0 = time_ns()
                r = alphaprove(
                    t,
                    f,
                    a[2],
                    rng=brng,
                    timeout=max_timeout
                )
                t1 = time_ns()

                if isnothing(r)
                    timeouts_classic += 1
                else
                    if r
                        val += 1
                    else
                        unval +=1
                    end
                end

                t2 = time_ns()
                r_hybrid = hybridalphaprove(
                    t_hybrid,
                    f_hybrid,
                    a[3],
                    rng=brng,
                    timeout=max_timeout
                )
                t3 = time_ns()

                if isnothing(r_hybrid)
                    timeouts_hybrid += 1
                else
                    if r_hybrid
                        val_hybrid += 1
                    else
                        unval_hybrid +=1
                    end
                end

                if !isnothing(r) && !isnothing(r_hybrid)
                    if r != r_hybrid
                        # @warn "Tableaux don't agree for formula $f, classic says $r, hybrid says $r_hybrid"
                        error("Tableaux don't agree for formula $f")
                    else
                        # Evaluate avg execution time only if both tableaux didn't timeout
                        e_time += t1-t0
                        e_time_hybrid += t3-t2
                    end
                else
                    timeouts+=1
                end

                if j == max_avg
                    break
                end
            end
            if i == max_it
                @warn "Warning: maximum iterations reached"
            end
        end

        # Verbose
        verbose && println("\nClassic Tableau")
        verbose && println(string(timeouts_classic) * " formulas over " * string(max_avg) * " timeout.")
        verbose && println("(" * string(max_avg - timeouts_classic) * " didn't.)")
        verbose && print("Average execution time (over " * string(max_avg - timeouts) * " formulas): ")
        verbose && println(string((e_time/1e6)/(max_avg - timeouts)) * " ms")
        verbose && println("$val/$(max_avg - timeouts_classic) formulas were α-val, " *
                "$unval/$(max_avg - timeouts_classic) formulas were not α-val\n")

        verbose && println("\nHybrid Tableau")
        verbose && println(string(timeouts_hybrid) * " formulas over " * string(max_avg) * " timeout.")
        verbose && println("(" * string(max_avg - timeouts_hybrid) * " didn't.)")
        verbose && print("Average execution time (over " * string(max_avg - timeouts) * " formulas): ")
        verbose && println(string((e_time_hybrid/1e6)/(max_avg - timeouts_hybrid)) * " ms")
        verbose && println("$val_hybrid/$(max_avg - timeouts) formulas were α-val, " *
                "$unval_hybrid/$(max_avg - timeouts_hybrid) formulas were not α-val\n")

        # Latex
        ntos[height-min_height+1] = max_avg - timeouts_classic
        tot_timeouts[findall(x->x==a, algebras)...] += timeouts_classic
        tot_val[findall(x->x==a, algebras)...] += val
        tot_unval[findall(x->x==a, algebras)...] += unval

        ntos_hybrid[height-min_height+1] = max_avg - timeouts_hybrid
        tot_timeouts_hybrid[findall(x->x==a, algebras)...] += timeouts_hybrid
        tot_val_hybrid[findall(x->x==a, algebras)...] += val_hybrid
        tot_unval_hybrid[findall(x->x==a, algebras)...] += unval_hybrid
    end

    # Latex
    println("\n\nCLassic Tableau")
    println("$(a[1])")
    for i in 1:length(ntos)
        print("($(i+min_height-1),$(ntos[i]))")
    end
    println("\n\nHybrid Tableau")
    println("$(a[1])")
    for i in 1:length(ntos_hybrid)
        print("($(i+min_height-1),$(ntos_hybrid[i]))")
    end
    println("\n\n")
end

# Latex
println("\n\nClassic Tableau")
println("\n\nTimeouts")
for i in 1:length(tot_timeouts)
    print("({$(algebras[i][1])},$(tot_timeouts[i]))")
end
println("\n\nalphaprove")
for i in 1:length(tot_val)
    print("({$(algebras[i][1])},$(tot_val[i]))")
end
println("\n\nNot alphaprove")
for i in 1:length(tot_unval)
    print("({$(algebras[i][1])},$(tot_unval[i]))")
end
println("\n\nHybrid Tableau")
println("\n\nTimeouts")
for i in 1:length(tot_timeouts_hybrid)
    print("({$(algebras[i][1])},$(tot_timeouts_hybrid[i]))")
end
println("\n\nalphaprove")
for i in 1:length(tot_val_hybrid)
    print("({$(algebras[i][1])},$(tot_val_hybrid[i]))")
end
println("\n\nNot alphaprove")
for i in 1:length(tot_unval_hybrid)
    print("({$(algebras[i][1])},$(tot_unval_hybrid[i]))")
end
println()
