using Graphs, Random
using SoleReasoners: sat, unsat, val, unval

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

k = parseformula("□(p→q)→(□p→□q)")
n = parseformula("◊p∧□¬p")

@test sat(k, e)
@test !unsat(k, e)
@test val(k, e)
@test !unval(k, e)

@test !sat(n, e)
@test unsat(n, e)
@test !val(n, e)
@test unval(n, e)
