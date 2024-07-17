using Random
using SoleLogics
using SoleLogics.ManyValuedLogics
using SoleReasoners
using StatsBase
import SoleBase: initrng
import SoleLogics: sample

BASE_MANY_VALUED_CONNECTIVES = [
    ∨,
    ∧,
    →
]
BaseManyValuedConnectives = Union{typeof.(BASE_MANY_VALUED_CONNECTIVES)...}

myalphabet = Atom.(["p", "q", "r"])

min_height = 3
max_height = 5
max_it = 2000
max_avg = 100
max_timeout = 10 # seconds
verbose = false

using SoleLogics.ManyValuedLogics: booleanalgebra, G3, Ł3, G4, Ł4, H4
using SoleLogics.ManyValuedLogics: G5, G6, H6_1, H6_2, H6_3, H6

algebras = [
    ("BA",   booleanalgebra),
    ("G3",   G3),
    ("Ł3",   Ł3),
    ("G4",   G4),
    ("Ł4",   Ł4),
    ("H4",   H4),
    ("G5",   G5),
    ("G6",   G6),
    ("H6_1", H6_1),
    ("H6_2", H6_2),
    ("H6_3", H6_3),
    ("H6",   H6)
]

# Latex
tot_timeouts = zeros(Int64, length(algebras))   # tot timeouts for each algebra
tot_val = zeros(Int64, length(algebras))        # tot val for each algebra
tot_unval = zeros(Int64, length(algebras))      # tot unval for each algebra

for a in algebras
    # Latex
    ntos = zeros(Int64, max_height-min_height+1)   # not timeout for each height  

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
        verbose && println("Alphaprove on " * a[1] * " formulas of height " * string(height))
        e_time = 0
        j = 0
        val = 0
        unval = 0
        timeouts = 0
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
                    timeouts += 1
                else
                    e_time += t1-t0
                    if r
                        val += 1
                    else
                        unval +=1
                    end
                end
                if j == max_avg
                    break
                end
            end
            if i == max_it
                @warn "Warning: maximum iterations reached"
            end
        end
        verbose && println(string(timeouts) * " formulas over " * string(max_avg) * " timeout.")
        verbose && println("(" * string(max_avg - timeouts) * " didn't.)")
        verbose && print("Average execution time (over " * string(max_avg - timeouts) * " formulas): ")
        verbose && println(string((e_time/1e6)/(max_avg - timeouts)) * " ms\n")
        verbose && println("$val/$(max_avg - timeouts) formulas were α-val, " *
                "$unval/$(max_avg - timeouts) formulas were not α-val\n")
        
        # Latex
        ntos[height-min_height+1] = max_avg - timeouts
        tot_timeouts[findall(x->x==a, algebras)...] += timeouts
        tot_val[findall(x->x==a, algebras)...] += val
        tot_unval[findall(x->x==a, algebras)...] += unval
    end
    
    # Latex
    println("$(a[1])")
    for i in 1:length(ntos)
        print("($(i+min_height-1),$(ntos[i]))")
    end
    println("\n\n")
end

# Latex
println("\nTimeouts")
for i in 1:length(tot_timeouts)
    print("({$(algebras[i][1])},$(tot_timeouts[i]))")
end
println("\n\nAlphaval")
for i in 1:length(tot_val)
    print("({$(algebras[i][1])},$(tot_val[i]))")
end
println("\n\nNot alphaval")
for i in 1:length(tot_unval)
    print("({$(algebras[i][1])},$(tot_unval[i]))")
end
println()
