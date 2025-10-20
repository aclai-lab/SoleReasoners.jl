using Graphs, Random, SoleLogics, StatsBase, Test, ThreadSafeDicts

# using TikzGraphs, TikzPictures

using SoleReasoners: sat, installspartacus, ssat

installspartacus()

rng = Xoshiro(42)
Σ = Atom.(["p","q","r","s","t"])
os = Vector{Connective}([∧, ∨, →, ¬, ◊, □])

aot = vcat(Σ, [⊤, ⊥])
aotpicker = (rng)->StatsBase.sample(rng, aot, StatsBase.uweights(length(aot)))

na = 5
maxw = 10
e = Vector{KripkeStructure}()
for nw in 2:maxw
    for ne in nw-1:nw*(nw-1)
        g = SimpleDiGraph(nw,ne)
        rem_vertices!(g, vertices(g)[map(v->!has_path(g,1,v),vertices(g))])
        # save(SVG("graph.svg"), plot(g))
        f = SoleLogics.ExplicitCrispUniModalFrame(SoleLogics.World.(1:nv(g)), g)
        v = Dict{
            SoleLogics.World{Int64},
            TruthDict{Dict{Atom{String}, BooleanTruth}}
        }()
        ws = f.worlds
        for i in 1:length(f.worlds)
            v[ws[i]] = TruthDict{Dict{Atom{String}, BooleanTruth}}()
            values = bitrand(rng, na)
            for j in 1:na
                v[ws[i]][Σ[j]] = values[j]
            end
        end
        push!(e, KripkeStructure(f, v))
    end
end

memo = ThreadSafeDict{KripkeStructure, ThreadSafeDict{Union{Atom, BooleanTruth, SyntaxBranch},Worlds{SoleLogics.World}}}()
for m in e
    memo[m] = ThreadSafeDict{Union{Atom, BooleanTruth, SyntaxBranch},Worlds{SoleLogics.World}}()
end

println("\nSATISFIABILITY")
tot_tp = 0
tot_fp = 0
tot_tn = 0
tot_fn = 0
tot_te = 0
tot_ts = 0
minh = 1
maxh = 50
nφ = 1
tte = zeros(Float16, maxh-minh+1)
tts = zeros(Float16, maxh-minh+1)
for h in minh:maxh
    tp = 0
    fp = 0
    tn = 0
    fn = 0
    te = 0
    ts = 0
    println("\nh=$h")
    for i in 1:nφ
        φ = randformula(
            rng,
            h,
            Σ,
            os,
            opweights = StatsBase.uweights(length(os)),
            basecase = aotpicker,
            mode = :full
        )
        t0 = time_ns()
        # re = sat(φ, e; memo=memo)
        te += time_ns() - t0
        t0 = time_ns()
        rs = ssat(φ; timeout = 60)
        ts += time_ns() - t0
        # if rs
        #     if re
        #         tp += 1
        #     else
        #         fn += 1
        #     end
        # else
        #     if re
        #         fp += 1
        #     else
        #         tn += 1
        #     end
        # end
    end
    global tot_tp += tp
    global tot_fp += fp
    global tot_tn += tn
    global tot_fn += fn
    global tot_te += te
    global tot_ts += ts
    println("TP: $tp\tFP: $fp\tTN: $tn\tFN: $fn")
    println("Embdegging avg. time: $(te/nφ) ns")
    println("Spartacus avg. time: $(ts/nφ) ns")
    tte[h-minh+1] = te/nφ
    tts[h-minh+1] = ts/nφ
end
println("\nRESULTS:")
println("TP: $tot_tp\tFP: $tot_fp\tTN: $tot_tn\tFN: $tot_fn")
println("Embdegging avg. time: $(tot_te/((maxh-minh+1)*nφ)) ns")
println("Spartacus avg. time: $(tot_ts/((maxh-minh+1)*nφ)) ns")
println("LATEX: ")
println("Embedding:")
for i in 1:length(tte)
    print("($(i+minh-1),$(tte[i]))")
end
println("Spartacus:")
for i in 1:length(tte)
    print("($(i+minh-1),$(tte[i]))")
end
println("\n\n")