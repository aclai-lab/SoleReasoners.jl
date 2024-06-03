using SoleLogics
using SoleLogics.ManyValuedLogics
using SoleReasoners
using Test

include("mvhs/afslos.jl")

include("mvhs/mvhsalphasat.jl")

include("mvhs/mvhsalphaprove.jl")

# p, q = Atom.(["p", "q"])
# diamondA = diamond(IA_A)
# boxA = box(IA_A)

# @test mvhsalphasat(
#     ⊥,
#     ∧(diamondA(p), boxA(→(p, ⊥))),
#     FiniteHeytingAlgebra(G3),
#     verbose=false
# ) == true
# @test mvhsalphasat(
#     α,
#     ∧(diamondA(p), boxA(→(p, ⊥))),
#     FiniteHeytingAlgebra(G3),
#     verbose=false
# ) == false
# @test mvhsalphasat(
#     ⊤,
#     ∧(diamondA(p), boxA(→(p, ⊥))),
#     FiniteHeytingAlgebra(G3),
#     verbose=false
# ) == false
