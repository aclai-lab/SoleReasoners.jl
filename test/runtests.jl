using SoleLogics
using SoleLogics.ManyValuedLogics
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
    ("Sat", ["sat.jl",]),
    ("HeytingAlphaSat", ["heytingalphasat.jl",]),
    ("HeytingAlphaProve", ["heytingalphaprove.jl",]),
    ("AlphaSat", ["alphasat.jl",]),
    ("AlphaProve", ["alphaprove.jl",]),
    (
        "BackwardCompatibility - Alphasat - booleanalgebra",
        ["backwardcompatibility/alphasat/booleanalgebra.jl"]
    ),
    (
        "BackwardCompatibility - Alphasat - G3",
        ["backwardcompatibility/alphasat/G3.jl"]
    ),
    (
        "BackwardCompatibility - Alphasat - G4",
        ["backwardcompatibility/alphasat/G4.jl"]
    ),
    (
        "BackwardCompatibility - Alphasat - H4",
        ["backwardcompatibility/alphasat/H4.jl"]
    ),
    # (
    #     "BackwardCompatibility - Alphasat - H9",
    #     ["backwardcompatibility/alphasat/H9.jl"]
    # ),
    (
        "BackwardCompatibility - Alphaprove - booleanalgebra",
        ["backwardcompatibility/alphaprove/booleanalgebra.jl"]
    ),
    (
        "BackwardCompatibility - Alphaprove - G3",
        ["backwardcompatibility/alphaprove/G3.jl"]
    ),
    (
        "BackwardCompatibility - Alphaprove - G4",
        ["backwardcompatibility/alphaprove/G4.jl"]
    ),
    (
        "BackwardCompatibility - Alphaprove - H4",
        ["backwardcompatibility/alphaprove/H4.jl"]
    ),
    # (
    #     "BackwardCompatibility - Alphaprove - H9",
    #     ["backwardcompatibility/alphaprove/H9.jl"]
    # ),
    # ("MVHS", ["mvhs.jl"]),
    ("Utils", ["utils.jl"]),
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
