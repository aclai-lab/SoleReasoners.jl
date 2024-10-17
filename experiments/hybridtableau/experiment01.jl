using Random
using SoleLogics
using SoleLogics.ManyValuedLogics
using SoleReasoners
using StatsBase
import SoleBase: initrng
import SoleLogics: sample
using SoleLogics.ManyValuedLogics: booleanalgebra, G3, Ł3, G4, Ł4, H4, G5, G6, H6_1, H6_2, H6_3, H6
using SoleLogics.ManyValuedLogics: FiniteIndexFLewAlgebra, FiniteIndexTruth

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
verbose = false

algebras = [
    ("BA",   booleanalgebra, convert(FiniteIndexFLewAlgebra, booleanalgebra)),
    ("G3",   G3, convert(FiniteIndexFLewAlgebra, G3)),
    ("Ł3",   Ł3, convert(FiniteIndexFLewAlgebra, Ł3)),
    ("G4",   G4, convert(FiniteIndexFLewAlgebra, G4)),
    ("Ł4",   Ł4, convert(FiniteIndexFLewAlgebra, Ł4)),
    ("H4",   H4, convert(FiniteIndexFLewAlgebra, H4)),
    ("G5",   G5, convert(FiniteIndexFLewAlgebra, G5)),
    ("G6",   G6, convert(FiniteIndexFLewAlgebra, G6)),
    ("H6\$_1\$", H6_1, convert(FiniteIndexFLewAlgebra, H6_1)),
    ("H6\$_2\$", H6_2, convert(FiniteIndexFLewAlgebra, H6_2)),
    ("H6\$_3\$", H6_3, convert(FiniteIndexFLewAlgebra, H6_3)),
    ("H6",   H6, convert(FiniteIndexFLewAlgebra, H6))
]

# Latex
tot_sat = zeros(Int64, length(algebras))                # tot sat for each algebra
tot_unsat = zeros(Int64, length(algebras))              # tot unsat for each algebra
tot_timeouts = zeros(Int64, length(algebras))           # tot timeouts_classic for each algebra
tot_sat_hybrid = zeros(Int64, length(algebras))         # tot sat for each algebra
tot_unsat_hybrid = zeros(Int64, length(algebras))       # tot unsat for each algebra
tot_timeouts_hybrid = zeros(Int64, length(algebras))    # tot timeouts_classic for each algebra
# Experiment (for each algebra)
for a in algebras
    # Latex
    avg_exc_times = zeros(Float64, max_height-min_height+1)         # avg execution time for each height (CT)
    avg_exc_times_hybrid = zeros(Float64, max_height-min_height+1)  # avg execution time for each height (HT)
    sat = zeros(Int64, max_height-min_height+1)                     # sat formulas for each height (CT)
    sat_hybrid = zeros(Int64, max_height-min_height+1)              # sat formulas for each height (HT)
    unsat = zeros(Int64, max_height-min_height+1)                   # unsat formulas for each height (CT)
    unsat_hybrid = zeros(Int64, max_height-min_height+1)            # unsat formulas for each height (HT)
    timeouts = zeros(Int64, max_height-min_height+1)                # timeouts for each height (CT)
    timeouts_hybrid = zeros(Int64, max_height-min_height+1)         # timeouts for each height (HT)    
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
    # Experiment (for each height)
    for height in min_height:max_height
        verbose && println("alphasat on " * a[1] * " formulas of height " * string(height))
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
                r = alphasat(
                    t,
                    f,
                    a[2],
                    rng=brng,
                    timeout=max_timeout
                )
                t1 = time_ns()
                if isnothing(r)
                    timeouts[height] += 1
                    avg_exc_times[height] += max_timeout*1e3
                else
                    avg_exc_times[height] += (t1-t0)/1e6
                    if r
                        sat[height] += 1
                    else
                        unsat[height] +=1
                    end
                end
                t0 = time_ns()
                r_hybrid = hybridalphasat(
                    t_hybrid,
                    f_hybrid,
                    a[3],
                    rng=brng,
                    timeout=max_timeout
                )
                t1 = time_ns()
                if isnothing(r_hybrid)
                    timeouts_hybrid[height] += 1
                    avg_exc_times_hybrid[height] += max_timeout*1e3
                else
                    avg_exc_times_hybrid[height] += (t1-t0)/1e6
                    if r_hybrid
                        sat_hybrid[height] += 1
                    else
                        unsat_hybrid[height] +=1
                    end
                end
                if !isnothing(r) && !isnothing(r_hybrid) && r != r_hybrid
                    error("Tableaux don't agree for formula $f, classic says $r, hybrid says $r_hybrid")
                end
                if j == max_avg
                    break
                end
            end
            if i == max_it
                @warn "Warning: maximum iterations reached"
            end
        end
        # Latex
        avg_exc_times[height] = (avg_exc_times[height])/max_avg
        tot_sat[findall(x->x==a, algebras)...] += sat[height]
        tot_unsat[findall(x->x==a, algebras)...] += unsat[height]
        tot_timeouts[findall(x->x==a, algebras)...] += timeouts[height]

        avg_exc_times_hybrid[height] = (avg_exc_times_hybrid[height])/max_avg
        tot_sat_hybrid[findall(x->x==a, algebras)...] += sat_hybrid[height]
        tot_unsat_hybrid[findall(x->x==a, algebras)...] += unsat_hybrid[height]
        tot_timeouts_hybrid[findall(x->x==a, algebras)...] += timeouts_hybrid[height]
    end
    # Latex
    println("Results for $(a[1])")
    println("\nCLassic Tableau")
    println("\nAverage execution time for each height")
    for i in 1:length(avg_exc_times)
        print("($(i+min_height-1),$(avg_exc_times[i]))")
    end
    println("\nSat formulas for each height")
    for i in 1:length(sat)
        print("($(i+min_height-1),$(sat[i]))")
    end
    println("\nUnsat formulas for each height")
    for i in 1:length(unsat)
        print("($(i+min_height-1),$(unsat[i]))")
    end
    println("\nTimeouts for each height")
    for i in 1:length(timeouts)
        print("($(i+min_height-1),$(timeouts[i]))")
    end
    println("\n\nHybrid Tableau")
    println("\nAverage execution time for each height")
    for i in 1:length(avg_exc_times_hybrid)
        print("($(i+min_height-1),$(avg_exc_times_hybrid[i]))")
    end
    println("\nSat formulas for each height")
    for i in 1:length(sat_hybrid)
        print("($(i+min_height-1),$(sat_hybrid[i]))")
    end
    println("\nUnsat formulas for each height")
    for i in 1:length(unsat_hybrid)
        print("($(i+min_height-1),$(unsat_hybrid[i]))")
    end
    println("\nTimeouts for each height")
    for i in 1:length(timeouts_hybrid)
        print("($(i+min_height-1),$(timeouts_hybrid[i]))")
    end
    println("\n\n")
end

# Latex
println("\n\nClassic Tableau")
println("\n\nalphasat")
for i in 1:length(tot_sat)
    print("({$(algebras[i][1])},$(tot_sat[i]))")
end
println("\n\nNot alphasat")
for i in 1:length(tot_unsat)
    print("({$(algebras[i][1])},$(tot_unsat[i]))")
end
println("\n\nTimeouts")
for i in 1:length(tot_timeouts)
    print("({$(algebras[i][1])},$(tot_timeouts[i]))")
end
println("\n\n\n\nHybrid Tableau")
println("\n\nalphasat")
for i in 1:length(tot_sat_hybrid)
    print("({$(algebras[i][1])},$(tot_sat_hybrid[i]))")
end
println("\n\nNot alphasat")
for i in 1:length(tot_unsat_hybrid)
    print("({$(algebras[i][1])},$(tot_unsat_hybrid[i]))")
end
println("\n\nTimeouts")
for i in 1:length(tot_timeouts_hybrid)
    print("({$(algebras[i][1])},$(tot_timeouts_hybrid[i]))")
end
println()
