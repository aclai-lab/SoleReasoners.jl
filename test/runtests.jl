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
    ("PropositionalBooleanSat", ["propositionalbooleansat.jl",]),
    ("PropositionalFuzzySat", ["propositionalfuzzysat.jl",]),
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
