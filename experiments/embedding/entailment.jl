using Graphs, Random, SoleLogics, StatsBase, Test
# using TikzGraphs, TikzPictures

installspartacus()

rng = Xoshiro(42)
Σ = Atom.(["p","q","r","s","t"])
os = Vector{Connective}([∧, ∨, →, ¬, ◊, □])

aot = vcat(Σ, [⊤, ⊥])
aotpicker = (rng)->StatsBase.sample(rng, aot, StatsBase.uweights(length(aot)))

na = 5
e = Vector{KripkeStructure}()
for nw in 2:10
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

println("Entailment")
tp = 0
fp = 0
tn = 0
fn = 0
te = 0
ts = 0
minh = 6
maxh = 10
nφ = 10
for h in minh:maxh
    println("h=$h")
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
        ψ = randformula(
            rng,
            h,
            Σ,
            os,
            opweights = StatsBase.uweights(length(os)),
            basecase = aotpicker,
            mode = :full
        )
        t0 = time_ns()
        re = ent(φ, ψ, e)
        global te += time_ns() - t0
        t0 = time_ns()
        rs = sent(φ, ψ)
        global ts += time_ns() - t0
        if rs
            if re
                global tp += 1
            else
                global fn += 1
            end
        else
            if re
                global fp += 1
            else
                global tn += 1
            end
        end
    end
end
println("TP: $tp\tFP: $fp\tTN: $tn\tFN: $fn")
println("Embdegging avg. time: $(te/((maxh-minh+1)*nφ)) ns")
println("Spartacus avg. time: $(ts/((maxh-minh+1)*nφ)) ns")
