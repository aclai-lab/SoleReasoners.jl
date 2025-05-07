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
    # ("Sat", ["sat.jl",]),
    # ("HeytingAlphaSat", ["heytingalphasat.jl",]),
    # ("HeytingAlphaProve", ["heytingalphaprove.jl",]),
    # (
    #     "BackwardCompatibility - Alphasat - booleanalgebra",
    #     ["backwardcompatibility/alphasat/booleanalgebra.jl"]
    # ),
    # (
    #     "BackwardCompatibility - Alphasat - G3",
    #     ["backwardcompatibility/alphasat/G3.jl"]
    # ),
    # (
    #     "BackwardCompatibility - Alphasat - G4",
    #     ["backwardcompatibility/alphasat/G4.jl"]
    # ),
    # (
    #     "BackwardCompatibility - Alphasat - H4",
    #     ["backwardcompatibility/alphasat/H4.jl"]
    # ),
    # (
    #     "BackwardCompatibility - Alphasat - H9",
    #     ["backwardcompatibility/alphasat/H9.jl"]
    # ),
    # (
    #     "BackwardCompatibility - Alphaprove - booleanalgebra",
    #     ["backwardcompatibility/alphaprove/booleanalgebra.jl"]
    # ),
    # (
    #     "BackwardCompatibility - Alphaprove - G3",
    #     ["backwardcompatibility/alphaprove/G3.jl"]
    # ),
    # (
    #     "BackwardCompatibility - Alphaprove - G4",
    #     ["backwardcompatibility/alphaprove/G4.jl"]
    # ),
    # (
    #     "BackwardCompatibility - Alphaprove - H4",
    #     ["backwardcompatibility/alphaprove/H4.jl"]
    # ),
    # (
    #     "BackwardCompatibility - Alphaprove - H9",
    #     ["backwardcompatibility/alphaprove/H9.jl"]
    # ),
    # ("MVHS", ["mvhs.jl"]),
    # ("IndexAlphaSat", ["ialphasat.jl",]),
    # ("IndexAlphaProve", ["ialphaprove.jl",]),
    # ("HybridAlphaSat", ["hybridalphasat.jl"]),
    # ("HybridAlphaProve", ["hybridalphaprove.jl"]),
    # ("IndexHybridAlphaSat", ["ihybridalphasat.jl"]),
    # ("IndexHybridAlphaProve", ["ihybridalphaprove.jl"]),
    # ("IndexHybridAlphaSatBackwardCompatibility", ["ihybridalphasatbc.jl"]),
    # ("IndexHybridAlphaProveBackwardCompatibility", ["ihybridalphaprovebc.jl"]),
    # ("HybridMVHSTableau", ["hybrid-modal-tableau.jl"]),
    # ("HybridMVHSAlphaSat", ["hybrid-mvhs-sat-bc.jl"]),
    # ("HybridMVHSAlphaProve", ["hybrid-mvhs-prove-bc.jl"]),
    # ("Utils", ["utils.jl"]),

    ("Abstract Tableau", ["abstract-tableau/abstract-tableau.jl"]),
    (   "Metric Heap", [
            "metric-heap/metric-heap.jl",
            "metric-heap/metrics.jl"
        ]
    ),
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
            "many-valued-multi-modal-tableau.jl/mvltlfp-tableau.jl",
            "many-valued-multi-modal-tableau.jl/mvcl-tableau.jl",
            "many-valued-multi-modal-tableau.jl/mvhs-tableau.jl",
            "many-valued-multi-modal-tableau.jl/mvlrcc8-tableau.jl"
        ]
    ),
    (
        "α-sat",
        [
            "alphasat/many-valued-propositional-logic/G4.jl",
            "alphasat/many-valued-propositional-logic/L4.jl",
            "alphasat/many-valued-propositional-logic/H4.jl"
        ]
    ),
    (
        "α-val",
        [
            "alphaval/many-valued-propositional-logic/G4.jl",
            "alphaval/many-valued-propositional-logic/L4.jl",
            "alphaval/many-valued-propositional-logic/H4.jl"
        ]
    )
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
