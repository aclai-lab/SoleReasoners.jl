using SoleLogics
using SoleReasoners
using Test

function run_tests(list)
    println("\n" * ("#"^50))
    for test in list
        println("TEST: $test")
        include(test)
    end
end

println("Julia version: ", VERSION)

test_suites = [
    ("Abstract Tableau", ["abstract-tableau/abstract-tableau.jl"]),
    (   "Metric Heap", [
            "metric-heap/metric-heap.jl",
            "metric-heap/metrics.jl"
        ]
    ),
    ("Sat", ["propositional-tableau/sat.jl",]),
    (
        "Many-Valued Multi-Modal Logic",
        [
            "many-valued-multi-modal-logic/many-valued-linear-order.jl",
            "many-valued-multi-modal-logic/mvltlfp.jl",
            "many-valued-multi-modal-logic/mvcl.jl",
            "many-valued-multi-modal-logic/mvhs.jl",
            "many-valued-multi-modal-logic/mvlrcc8.jl"
        ]
    ),
    (
        "Many-Valued Multi-Modal Tableau",
        [
            "many-valued-multi-modal-tableau/many-valued-multi-modal-talbeau.jl",
            "many-valued-multi-modal-tableau/mvltlfp-tableau.jl",
            "many-valued-multi-modal-tableau/mvcl-tableau.jl",
            "many-valued-multi-modal-tableau/mvhs-tableau.jl",
            "many-valued-multi-modal-tableau/mvlrcc8-tableau.jl"
        ]
    ),
    (
        "α-sat",
        [
            "alphasat/mvltlfp-tableau/G4.jl",
            "alphasat/mvltlfp-tableau/L4.jl",
            "alphasat/mvltlfp-tableau/H4.jl",
            "alphasat/mvcl-tableau/H4.jl",
            "alphasat/mvhs-tableau/booleanalgebra.jl",
            "alphasat/mvhs-tableau/G4.jl",
            "alphasat/mvhs-tableau/L4.jl",
            "alphasat/mvhs-tableau/H4.jl",
            "alphasat/mvlrcc8-tableau/H4.jl"
        ]
    ),
    (
        "α-val",
        [
            "alphaval/mvltlfp-tableau/G4.jl",
            "alphaval/mvltlfp-tableau/L4.jl",
            "alphaval/mvltlfp-tableau/H4.jl",
            "alphaval/mvcl-tableau/H4.jl",
            "alphaval/mvhs-tableau/booleanalgebra.jl",
            "alphaval/mvhs-tableau/G4.jl",
            "alphaval/mvhs-tableau/L4.jl",
            "alphaval/mvhs-tableau/H4.jl",
            "alphaval/mvlrcc8-tableau/H4.jl"
        ]
    ),
    ("Utils", ["utils/utils.jl"]),
]

@testset "SoleReasoners.jl" begin
    for ts in eachindex(test_suites)
        name = test_suites[ts][1]
        list = test_suites[ts][2]
        let
            @testset "$name" begin
                run_tests(list)
            end
        end
    end
    println()
end
