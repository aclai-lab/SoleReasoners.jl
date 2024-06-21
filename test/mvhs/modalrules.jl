using SoleLogics: IA_O, converse # momentary fix
using SoleLogics.ManyValuedLogics: G3, H4, α, β

p, q = Atom.(["p", "q"])

diamondA = diamond(IA_A)
diamondL = diamond(IA_L)
diamondB = diamond(IA_B)
diamondE = diamond(IA_E)
diamondD = diamond(IA_D)
diamondO = diamond(IA_O)
diamondAi = diamond(IA_Ai)
diamondLi = diamond(IA_Li)
diamondBi = diamond(IA_Bi)
diamondEi = diamond(IA_Ei)
diamondDi = diamond(IA_Di)
diamondOi = diamond(IA_Oi)
boxA = box(IA_A)
boxL = box(IA_L)
boxB = box(IA_B)
boxE = box(IA_E)
boxD = box(IA_D)
boxO = box(IA_O)
boxAi = box(IA_Ai)
boxLi = box(IA_Li)
boxBi = box(IA_Bi)
boxEi = box(IA_Ei)
boxDi = box(IA_Di)
boxOi = box(IA_Oi)

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

# ###################################################
# # Examples from Fuzzy Sets and Systems 456 (2023) #
# ###################################################

# f, b = Atom.(["f", "b"])
# @test mvhsalphasat(
#     α,
#     ∧(f,diamondA(b)),
#     FiniteHeytingAlgebra(H4),
#     verbose=false
# ) == true

# for X in [IA_A, IA_L, IA_B, IA_E, IA_D, IA_O, IA_Ai, IA_Li, IA_Bi, IA_Ei, IA_Di, IA_Oi]
@test mvhsalphaprove(
    ⊤,
    →(
        boxA(→(p,q)),
        →(boxA(p),boxA(q))
    ),
    FiniteHeytingAlgebra(H4)
) == true
#     @test mvhsalphaprove(
#         ⊤,
#         →(
#             box(X)(→(p,q)),
#             →(box(X)p,box(X)q)
#         )
#     ) == true
#     @test mvhsalphaprove(
#         ⊤,
#         →(
#             box(X)(→(p,q)),
#             →(box(X)p,box(X)q)
#         )
#     ) == true
#     @test mvhsalphaprove(
#         ⊤,
#         →(
#             box(X)(→(p,q)),
#             →(box(X)p,box(X)q)
#         )
#     ) == true
#     @test mvhsalphaprove(
#         ⊤,
#         →(
#             box(X)(→(p,q)),
#             →(box(X)p,box(X)q)
#         )
#     ) == true
#     @test mvhsalphaprove(
#         ⊤,
#         →(
#             box(X)(→(p,q)),
#             →(box(X)p,box(X)q)
#         )
#     ) == true
#     @test mvhsalphaprove(
#         ⊤,
#         →(
#             box(X)(→(p,q)),
#             →(box(X)p,box(X)q)
#         )
#     ) == true
#     @test mvhsalphaprove(
#         ⊤,
#         →(
#             box(X)(→(p,q)),
#             →(box(X)p,box(X)q)
#         )
#     ) == true
#     @test mvhsalphaprove(
#         ⊤,
#         →(
#             box(X)(→(p,q)),
#             →(box(X)p,box(X)q)
#         )
#     ) == true
#     @test mvhsalphaprove(
#         ⊤,
#         →(
#             box(X)(→(p,q)),
#             →(box(X)p,box(X)q)
#         )
#     ) == true
#     @test mvhsalphaprove(
#         ⊤,
#         →(
#             box(X)(→(p,q)),
#             →(box(X)p,box(X)q)
#         )
#     ) == true
#     @test mvhsalphaprove(
#         ⊤,
#         →(
#             box(X)(→(p,q)),
#             →(box(X)p,box(X)q)
#         )
#     ) == true
# end

# for X in [IA_A, IA_L, IA_B, IA_E, IA_D, IA_O]
#     @test mvhsalphaprove(
#         ⊤,
#         →(
#             p,
#             box(X)diamond(converse(X))p
#         )
#     ) == true
# end
