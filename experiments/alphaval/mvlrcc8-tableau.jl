using Random
using SoleLogics
using SoleLogics.ManyValuedLogics
using SoleReasoners
using StatsBase
import SoleBase: initrng
import SoleLogics: sample

myalphabet = Atom.(["p", "q", "r"])

min_height = 1
max_height = 7
max_it = 99999
max_avg = 200
max_timeout = 60 # seconds

verbose = false

using SoleLogics: LRCC8_Rec_DC, LRCC8_Rec_EC, LRCC8_Rec_PO
using SoleLogics: LRCC8_Rec_TPP, LRCC8_Rec_TPPi, LRCC8_Rec_NTPP, LRCC8_Rec_NTPPi

mvlrcc8operators = Vector{Connective}(BASE_MANY_VALUED_CONNECTIVES)
append!(
    mvlrcc8operators,
    [
        diamond(LRCC8_Rec_DC),
        diamond(LRCC8_Rec_EC),
        diamond(LRCC8_Rec_PO),
        diamond(LRCC8_Rec_TPP),
        diamond(LRCC8_Rec_TPPi),
        diamond(LRCC8_Rec_NTPP),
        diamond(LRCC8_Rec_NTPPi),
        box(LRCC8_Rec_DC),
        box(LRCC8_Rec_EC),
        box(LRCC8_Rec_PO),
        box(LRCC8_Rec_TPP),
        box(LRCC8_Rec_TPPi),
        box(LRCC8_Rec_NTPP),
        box(LRCC8_Rec_NTPPi)
    ]
)
mvlrcc8opweights = [14, 14, 14, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3]

using SoleLogics.ManyValuedLogics: booleanalgebra, G3, Ł3, G4, Ł4, H4
using SoleLogics.ManyValuedLogics: G5, G6, H6_1, H6_2, H6_3, H6

algebras = [
    ("BA",   booleanalgebra),
    ("G3",   G3            ),
    ("Ł3",   Ł3            ),
    ("G4",   G4            ),
    ("Ł4",   Ł4            ),
    ("H4",   H4            ),
    # ("G5",   G5            ),
    # ("G6",   G6            ),
    # ("H6_1", H6_1          ),
    # ("H6_2", H6_2          ),
    # ("H6_3", H6_3          ),
    # ("H6",   H6            )
]

# Latex
tot_timeouts = zeros(Int64, length(algebras))   # tot timeouts for each algebra
tot_n_timeouts = zeros(Int64, length(algebras)) # tot no timeouts for each alg.
tot_val = zeros(Int64, length(algebras))        # tot val for each algebra
tot_unval = zeros(Int64, length(algebras))      # tot unval for each algebra

for a in algebras
    # Latex
    tos = zeros(Int64, max_height-min_height+1)     # timeouts for each height
    ntos = zeros(Int64, max_height-min_height+1)    # no timeout for each height
    vals = zeros(Int64, max_height-min_height+1)    # val for each height
    unvals = zeros(Int64, max_height-min_height+1)  # unval for each height
    times = zeros(Float16, max_height-min_height+1) # times for each height

    rng = initrng(Random.GLOBAL_RNG)
    aot = vcat(myalphabet,getdomain(a[2])) # atoms or truths
    aotweights = StatsBase.uweights(length(myalphabet)+length(getdomain(a[2])))
    aotpicker = (rng)->StatsBase.sample(rng, aot, aotweights)

    for height in min_height:max_height
        verbose && println("MVLRCC8 Alphaval on " * a[1] * " formulas of height " * string(height))
        e_time = 0
        j = 0
        val = 0
        unval = 0
        timeouts = 0
        for i in 1:max_it
            t = rand(MersenneTwister(i), getdomain(a[2]))
            f = randformula(
                MersenneTwister(i),
                height,
                myalphabet,
                mvlrcc8operators,
                opweights = mvlrcc8opweights,
                basecase = aotpicker,
                mode = :full
            )
            if !isbot(t) && SoleLogics.height(f) == height
                verbose && println("$t⪯$f")
                j += 1
                t0 = time_ns()
                r = alphaval(
                    MVLRCC8Tableau,
                    t,
                    f,
                    a[2],
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
                        unval += 1
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
        verbose && println(string(timeouts) * " formulas over " * string(max_avg) * " timeout.")
        verbose && println("(" * string(max_avg - timeouts) * " didn't.)")
        verbose && print("Average execution time (over " * string(max_avg - timeouts) * " formulas): ")
        verbose && println(string((e_time/1e6)/(max_avg - timeouts)) * " ms\n")
        verbose && println("$val/$(max_avg - timeouts) formulas were α-val, " *
                "$unval/$(max_avg - timeouts) formulas were not α-val\n")
        verbose && println()

        # Latex
        tos[height-min_height+1] = timeouts
        ntos[height-min_height+1] = max_avg - timeouts
        vals[height-min_height+1] = val
        unvals[height-min_height+1] = unval
        times[height-min_height+1] = (e_time/1e6)/(max_avg - timeouts)

        tot_timeouts[findall(x->x==a, algebras)...] += timeouts
        tot_n_timeouts[findall(x->x==a, algebras)...] += max_avg - timeouts
        tot_val[findall(x->x==a, algebras)...] += val
        tot_unval[findall(x->x==a, algebras)...] += unval

        flush(stdout)
    end

    # Latex
    println("$(a[1])")
    println("Timeouts:")
    for i in 1:length(tos)
        print("($(i+min_height-1),$(tos[i]))")
    end
    println("\nNo timeouts:")
    for i in 1:length(ntos)
        print("($(i+min_height-1),$(ntos[i]))")
    end
    println("\nVal:")
    for i in 1:length(vals)
        print("($(i+min_height-1),$(vals[i]))")
    end
    println("\nUnval:")
    for i in 1:length(unvals)
        print("($(i+min_height-1),$(unvals[i]))")
    end
    println("\nTimes:")
    for i in 1:length(unvals)
        print("($(i+min_height-1),$(times[i]))")
    end
    println("\n\n")
end

# Latex
println("\nTimeouts")
for i in 1:length(tot_timeouts)
    print("({$(algebras[i][1])},$(tot_timeouts[i]))")
end
println("\nNo timeouts")
for i in 1:length(tot_n_timeouts)
    print("({$(algebras[i][1])},$tot_n_timeouts)")
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
