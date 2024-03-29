using SoleLogics
using SoleLogics.ManyValuedLogics
using SoleLogics.ManyValuedLogics: BASE_MANY_VALUED_CONNECTIVES

# α = FiniteTruth("α")
# β = FiniteTruth("β")
# γ = FiniteTruth("γ")
# δ = FiniteTruth("δ")
# ε = FiniteTruth("ε")
# ζ = FiniteTruth("ζ")
# η = FiniteTruth("η")

# d9 = Vector{FiniteTruth}([⊥, α, β, γ, δ, ε, ζ, η, ⊤])

# jointable = Dict{Tuple{FiniteTruth, FiniteTruth}, FiniteTruth}(
#     (⊥, ⊥) => ⊥, (⊥, α) => α, (⊥, β) => β, (⊥, γ) => γ, (⊥, δ) => δ, (⊥, ε) => ε, (⊥, ζ) => ζ, (⊥, η) => η, (⊥, ⊤) => ⊤,
#     (α, ⊥) => α, (α, α) => α, (α, β) => δ, (α, γ) => γ, (α, δ) => δ, (α, ε) => η, (α, ζ) => ζ, (α, η) => η, (α, ⊤) => ⊤,
#     (β, ⊥) => β, (β, α) => δ, (β, β) => β, (β, γ) => ζ, (β, δ) => δ, (β, ε) => ε, (β, ζ) => ζ, (β, η) => η, (β, ⊤) => ⊤,
#     (γ, ⊥) => γ, (γ, α) => γ, (γ, β) => ζ, (γ, γ) => γ, (γ, δ) => ζ, (γ, ε) => ⊤, (γ, ζ) => ζ, (γ, η) => ⊤, (γ, ⊤) => ⊤,
#     (δ, ⊥) => δ, (δ, α) => δ, (δ, β) => δ, (δ, γ) => ζ, (δ, δ) => δ, (δ, ε) => η, (δ, ζ) => ζ, (δ, η) => η, (δ, ⊤) => ⊤,
#     (ε, ⊥) => ε, (ε, α) => η, (ε, β) => ε, (ε, γ) => ⊤, (ε, δ) => η, (ε, ε) => ε, (ε, ζ) => ⊤, (ε, η) => η, (ε, ⊤) => ⊤,
#     (ζ, ⊥) => ζ, (ζ, α) => ζ, (ζ, β) => ζ, (ζ, γ) => ζ, (ζ, δ) => ζ, (ζ, ε) => ⊤, (ζ, ζ) => ζ, (ζ, η) => ⊤, (ζ, ⊤) => ⊤,
#     (η, ⊥) => η, (η, α) => η, (η, β) => η, (η, γ) => ⊤, (η, δ) => η, (η, ε) => η, (η, ζ) => ⊤, (η, η) => η, (η, ⊤) => ⊤,
#     (⊤, ⊥) => ⊤, (⊤, α) => ⊤, (⊤, β) => ⊤, (⊤, γ) => ⊤, (⊤, δ) => ⊤, (⊤, ε) => ⊤, (⊤, ζ) => ⊤, (⊤, η) => ⊤, (⊤, ⊤) => ⊤
# )

# meettable = Dict{Tuple{FiniteTruth, FiniteTruth}, FiniteTruth}(
#     (⊥, ⊥) => ⊥, (⊥, α) => ⊥, (⊥, β) => ⊥, (⊥, γ) => ⊥, (⊥, δ) => ⊥, (⊥, ε) => ⊥, (⊥, ζ) => ⊥, (⊥, η) => ⊥, (⊥, ⊤) => ⊥,
#     (α, ⊥) => ⊥, (α, α) => α, (α, β) => ⊥, (α, γ) => α, (α, δ) => α, (α, ε) => ⊥, (α, ζ) => α, (α, η) => α, (α, ⊤) => α,
#     (β, ⊥) => ⊥, (β, α) => ⊥, (β, β) => β, (β, γ) => ⊥, (β, δ) => β, (β, ε) => β, (β, ζ) => β, (β, η) => β, (β, ⊤) => β,
#     (γ, ⊥) => ⊥, (γ, α) => α, (γ, β) => ⊥, (γ, γ) => γ, (γ, δ) => α, (γ, ε) => ⊥, (γ, ζ) => γ, (γ, η) => α, (γ, ⊤) => γ,
#     (δ, ⊥) => ⊥, (δ, α) => α, (δ, β) => β, (δ, γ) => α, (δ, δ) => δ, (δ, ε) => β, (δ, ζ) => δ, (δ, η) => δ, (δ, ⊤) => δ,
#     (ε, ⊥) => ⊥, (ε, α) => ⊥, (ε, β) => β, (ε, γ) => ⊥, (ε, δ) => β, (ε, ε) => ε, (ε, ζ) => β, (ε, η) => ε, (ε, ⊤) => ε,
#     (ζ, ⊥) => ⊥, (ζ, α) => α, (ζ, β) => β, (ζ, γ) => γ, (ζ, δ) => δ, (ζ, ε) => β, (ζ, ζ) => ζ, (ζ, η) => δ, (ζ, ⊤) => ζ,
#     (η, ⊥) => ⊥, (η, α) => α, (η, β) => β, (η, γ) => α, (η, δ) => δ, (η, ε) => ε, (η, ζ) => δ, (η, η) => η, (η, ⊤) => η,
#     (⊤, ⊥) => ⊥, (⊤, α) => α, (⊤, β) => β, (⊤, γ) => γ, (⊤, δ) => δ, (⊤, ε) => ε, (⊤, ζ) => ζ, (⊤, η) => η, (⊤, ⊤) => ⊤
# )

# join = BinaryOperation(d9, jointable)

# meet = BinaryOperation(d9, meettable)

# monoid = CommutativeMonoid(meet, ⊤)

# ffa9 = FiniteFLewAlgebra(join, meet, monoid, ⊥, ⊤)

# fha9 = FiniteHeytingAlgebra(ffa9)

# println(fha9)

# ############################################################################################
# #### Boolean algebra #######################################################################
# ############################################################################################

# d2 = Vector{BooleanTruth}([⊥, ⊤])
# jt2 = Dict{Tuple{BooleanTruth, BooleanTruth}, BooleanTruth}(
#     (⊥, ⊥) => ⊥, (⊥, ⊤) => ⊤,
#     (⊤, ⊥) => ⊤, (⊤, ⊤) => ⊤
# )
# mt2 = Dict{Tuple{BooleanTruth, BooleanTruth}, BooleanTruth}(
#     (⊥, ⊥) => ⊥, (⊥, ⊤) => ⊥,
#     (⊤, ⊥) => ⊥, (⊤, ⊤) => ⊤
# )
# j2 = BinaryOperation(d2, jt2)
# m2 = BinaryOperation(d2, mt2)
# mm2 = CommutativeMonoid(m2, ⊤)
# ffa2 = FiniteFLewAlgebra(j2, m2, mm2, ⊥, ⊤)
# fha2 = FiniteHeytingAlgebra(ffa2)

# ############################################################################################
# #### Three-valued algebra ##################################################################
# ############################################################################################

# d3 = Vector{FiniteTruth}([⊥, α, ⊤])
# jt3 = Dict{Tuple{FiniteTruth, FiniteTruth}, FiniteTruth}(
#     (⊥, ⊥) => ⊥, (⊥, α) => α, (⊥, ⊤) => ⊤,
#     (α, ⊥) => α, (α, α) => α, (α, ⊤) => ⊤,
#     (⊤, ⊥) => ⊤, (⊤, α) => ⊤, (⊤, ⊤) => ⊤
# )
# mt3 = Dict{Tuple{FiniteTruth, FiniteTruth}, FiniteTruth}(
#     (⊥, ⊥) => ⊥, (⊥, α) => ⊥, (⊥, ⊤) => ⊥,
#     (α, ⊥) => ⊥, (α, α) => α, (α, ⊤) => α,
#     (⊤, ⊥) => ⊥, (⊤, α) => α, (⊤, ⊤) => ⊤
# )
# j3 = BinaryOperation(d3, jt3)
# m3 = BinaryOperation(d3, mt3)
# mm3 = CommutativeMonoid(m3, ⊤)
# ffa3 = FiniteFLewAlgebra(j3, m3, mm3, ⊥, ⊤)
# fha3 = FiniteHeytingAlgebra(ffa3)

# ############################################################################################
# #### Diamond algebra #######################################################################
# ############################################################################################

# d4 = Vector{FiniteTruth}([⊥, α, β, ⊤])
# jt4 = Dict{Tuple{FiniteTruth, FiniteTruth}, FiniteTruth}(
#     (⊥, ⊥) => ⊥, (⊥, α) => α, (⊥, β) => β, (⊥, ⊤) => ⊤,
#     (α, ⊥) => α, (α, α) => α, (α, β) => ⊤, (α, ⊤) => ⊤,
#     (β, ⊥) => β, (β, α) => ⊤, (β, β) => β, (β, ⊤) => ⊤,
#     (⊤, ⊥) => ⊤, (⊤, α) => ⊤, (⊤, β) => ⊤, (⊤, ⊤) => ⊤
# )
# mt4 = Dict{Tuple{FiniteTruth, FiniteTruth}, FiniteTruth}(
#     (⊥, ⊥) => ⊥, (⊥, α) => ⊥, (⊥, β) => ⊥, (⊥, ⊤) => ⊥,
#     (α, ⊥) => ⊥, (α, α) => α, (α, β) => ⊥, (α, ⊤) => α,
#     (β, ⊥) => ⊥, (β, α) => ⊥, (β, β) => β, (β, ⊤) => β,
#     (⊤, ⊥) => ⊥, (⊤, α) => α, (⊤, β) => β, (⊤, ⊤) => ⊤
# )
# j4 = BinaryOperation(d4, jt4)
# m4 = BinaryOperation(d4, mt4)
# mm4 = CommutativeMonoid(m4, ⊤)
# ffa4 = FiniteFLewAlgebra(j4, m4, mm4, ⊥, ⊤)
# fha4 = FiniteHeytingAlgebra(ffa4)

# ############################################################################################
# #### SAT ###################################################################################
# ############################################################################################

# @test sat(parseformula("⊥"),   fha2) == false
# @test sat(parseformula("⊤"),   fha2) == true
# @test sat(parseformula("⊥∧⊥"), fha2) == false
# @test sat(parseformula("⊥∧⊤"), fha2) == false
# @test sat(parseformula("⊤∧⊥"), fha2) == false
# @test sat(parseformula("⊤∧⊤"), fha2) == true
# @test sat(parseformula("⊥∨⊥"), fha2) == false
# @test sat(parseformula("⊥∨⊤"), fha2) == true
# @test sat(parseformula("⊤∨⊥"), fha2) == true
# @test sat(parseformula("⊤∨⊤"), fha2) == true
# @test sat(parseformula("⊥→⊥"), fha2) == true
# @test sat(parseformula("⊥→⊤"), fha2) == true
# @test sat(parseformula("⊤→⊥"), fha2) == false
# @test sat(parseformula("⊤→⊤"), fha2) == true

# @test sat(parseformula("⊥"),   fha3) == false
# @test sat(parseformula("⊤"),   fha3) == true
# @test sat(parseformula("⊥∧⊥"), fha3) == false
# @test sat(parseformula("⊥∧⊤"), fha3) == false
# @test sat(parseformula("⊤∧⊥"), fha3) == false
# @test sat(parseformula("⊤∧⊤"), fha3) == true
# @test sat(parseformula("⊥∨⊥"), fha3) == false
# @test sat(parseformula("⊥∨⊤"), fha3) == true
# @test sat(parseformula("⊤∨⊥"), fha3) == true
# @test sat(parseformula("⊤∨⊤"), fha3) == true
# @test sat(parseformula("⊥→⊥"), fha3) == true
# @test sat(parseformula("⊥→⊤"), fha3) == true
# @test sat(parseformula("⊤→⊥"), fha3) == false
# @test sat(parseformula("⊤→⊤"), fha3) == true

# @test sat(parseformula("⊥"),   fha4) == false
# @test sat(parseformula("⊤"),   fha4) == true
# @test sat(parseformula("⊥∧⊥"), fha4) == false
# @test sat(parseformula("⊥∧⊤"), fha4) == false
# @test sat(parseformula("⊤∧⊥"), fha4) == false
# @test sat(parseformula("⊤∧⊤"), fha4) == true
# @test sat(parseformula("⊥∨⊥"), fha4) == false
# @test sat(parseformula("⊥∨⊤"), fha4) == true
# @test sat(parseformula("⊤∨⊥"), fha4) == true
# @test sat(parseformula("⊤∨⊤"), fha4) == true
# @test sat(parseformula("⊥→⊥"), fha4) == true
# @test sat(parseformula("⊥→⊤"), fha4) == true
# @test sat(parseformula("⊤→⊥"), fha4) == false
# @test sat(parseformula("⊤→⊤"), fha4) == true

# @test sat(parseformula("p"), fha2) == true
# @test sat(parseformula("p→⊥"), fha2) == true
# @test sat(parseformula("p∧p"), fha2) == true
# @test sat(parseformula("p∧(p→⊥)"), fha2) == false
# @test sat(parseformula("(p→⊥)∧p"), fha2) == false
# @test sat(parseformula("(p→⊥)∧(p→⊥)"), fha2) == true
# @test sat(parseformula("p∨p"), fha2) == true
# @test sat(parseformula("p∨(p→⊥)"), fha2) == true
# @test sat(parseformula("(p→⊥)∨p"), fha2) == true
# @test sat(parseformula("(p→⊥)∨(p→⊥)"), fha2) == true
# @test sat(parseformula("p→p"), fha2) == true
# @test sat(parseformula("p→(p→⊥)"), fha2) == true
# @test sat(parseformula("(p→⊥)→p"), fha2) == true
# @test sat(parseformula("(p→⊥)→(p→⊥)"), fha2) == true

# @test sat(parseformula("p"), fha3) == true
# @test sat(parseformula("p→⊥"), fha3) == true
# @test sat(parseformula("p∧p"), fha3) == true
# @test sat(parseformula("p∧(p→⊥)"), fha3) == false
# @test sat(parseformula("(p→⊥)∧p"), fha3) == false
# @test sat(parseformula("(p→⊥)∧(p→⊥)"), fha3) == true
# @test sat(parseformula("p∨p"), fha3) == true
# @test sat(parseformula("p∨(p→⊥)"), fha3) == true
# @test sat(parseformula("(p→⊥)∨p"), fha3) == true
# @test sat(parseformula("(p→⊥)∨(p→⊥)"), fha3) == true
# @test sat(parseformula("p→p"), fha3) == true
# @test sat(parseformula("p→(p→⊥)"), fha3) == true
# @test sat(parseformula("(p→⊥)→p"), fha3) == true
# @test sat(parseformula("(p→⊥)→(p→⊥)"), fha3) == true

# @test sat(parseformula("p"), fha4) == true
# @test sat(parseformula("p→⊥"), fha4) == true
# @test sat(parseformula("p∧p"), fha4) == true
# @test sat(parseformula("p∧(p→⊥)"), fha4) == false
# @test sat(parseformula("(p→⊥)∧p"), fha4) == false
# @test sat(parseformula("(p→⊥)∧(p→⊥)"), fha4) == true
# @test sat(parseformula("p∨p"), fha4) == true
# @test sat(parseformula("p∨(p→⊥)"), fha4) == true
# @test sat(parseformula("(p→⊥)∨p"), fha4) == true
# @test sat(parseformula("(p→⊥)∨(p→⊥)"), fha4) == true
# @test sat(parseformula("p→p"), fha4) == true
# @test sat(parseformula("p→(p→⊥)"), fha4) == true
# @test sat(parseformula("(p→⊥)→p"), fha4) == true
# @test sat(parseformula("(p→⊥)→(p→⊥)"), fha4) == true

# @test sat(
#     parseformula(
#         "(x∨y∨z)∧(x∨y∨(z→⊥))∧(x∨(y→⊥)∨z)∧(x∨(y→⊥)∨(z→⊥))∧" *
#         "((x→⊥)∨y∨z)∧((x→⊥)∨y∨(z→⊥))∧((x→⊥)∨(y→⊥)∨z)∧((x→⊥)∨(y→⊥)∨z)"
#     ),
#     fha2
# ) == true

# @test sat(
#     parseformula(
#         "(x∨y∨z)∧(x∨y∨(z→⊥))∧(x∨(y→⊥)∨z)∧(x∨(y→⊥)∨(z→⊥))∧" *
#         "((x→⊥)∨y∨z)∧((x→⊥)∨y∨(z→⊥))∧((x→⊥)∨(y→⊥)∨z)∧((x→⊥)∨(y→⊥)∨(z→⊥))"
#     ),
#     fha2
# ) == false

# @test sat(
#     parseformula(
#         "(x∨y∨z)∧(x∨y∨(z→⊥))∧(x∨(y→⊥)∨z)∧(x∨(y→⊥)∨(z→⊥))∧" *
#         "((x→⊥)∨y∨z)∧((x→⊥)∨y∨(z→⊥))∧((x→⊥)∨(y→⊥)∨z)∧((x→⊥)∨(y→⊥)∨z)"
#     ),
#     fha3
# ) == true

# @test sat(
#     parseformula(
#         "(x∨y∨z)∧(x∨y∨(z→⊥))∧(x∨(y→⊥)∨z)∧(x∨(y→⊥)∨(z→⊥))∧" *
#         "((x→⊥)∨y∨z)∧((x→⊥)∨y∨(z→⊥))∧((x→⊥)∨(y→⊥)∨z)∧((x→⊥)∨(y→⊥)∨(z→⊥))"
#     ),
#     fha3
# ) == false

# @test sat(
#     parseformula(
#         "(x∨y∨z)∧(x∨y∨(z→⊥))∧(x∨(y→⊥)∨z)∧(x∨(y→⊥)∨(z→⊥))∧" *
#         "((x→⊥)∨y∨z)∧((x→⊥)∨y∨(z→⊥))∧((x→⊥)∨(y→⊥)∨z)∧((x→⊥)∨(y→⊥)∨z)"
#     ),
#     fha4
# ) == true

# @test sat(
#     parseformula(
#         "(x∨y∨z)∧(x∨y∨(z→⊥))∧(x∨(y→⊥)∨z)∧(x∨(y→⊥)∨(z→⊥))∧" *
#         "((x→⊥)∨y∨z)∧((x→⊥)∨y∨(z→⊥))∧((x→⊥)∨(y→⊥)∨z)∧((x→⊥)∨(y→⊥)∨(z→⊥))"
#     ),
#     fha4
# ) == false

# # @test sat(
# #     booleantofuzzy(dimacstosole("benchmark/sat/uf50-01.cnf")),
# #     fha2
# # ) == true

# # @test sat(
# #     booleantofuzzy(dimacstosole("benchmark/sat/uf50-01.cnf")),
# #     fha3
# # ) == true

# # @test sat(
# #     booleantofuzzy(dimacstosole("benchmark/sat/uf50-01.cnf")),
# #     fha4
# # ) == true

# # @test sat(
# #     booleantofuzzy(dimacstosole("benchmark/sat/uf50-02.cnf")),
# #     fha2
# # ) == true

# # @test sat(
# #     booleantofuzzy(dimacstosole("benchmark/sat/uf50-02.cnf")),
# #     fha3
# # ) == true

# # @test sat(
# #     booleantofuzzy(dimacstosole("benchmark/sat/uf50-02.cnf")),
# #     fha4
# # ) == true

# @test alphasat(⊥, ⊥,       fha3) == true
# @test alphasat(⊥, α,       fha3) == true
# @test alphasat(⊥, ⊤,       fha3) == true
# @test alphasat(⊥, ∧(⊥, ⊥), fha3) == true
# @test alphasat(⊥, ∧(⊥, α), fha3) == true
# @test alphasat(⊥, ∧(⊥, ⊤), fha3) == true
# @test alphasat(⊥, ∧(α, ⊥), fha3) == true
# @test alphasat(⊥, ∧(α, α), fha3) == true
# @test alphasat(⊥, ∧(α, ⊤), fha3) == true
# @test alphasat(⊥, ∧(⊤, ⊥), fha3) == true
# @test alphasat(⊥, ∧(⊤, α), fha3) == true
# @test alphasat(⊥, ∧(⊤, ⊤), fha3) == true
# @test alphasat(⊥, ∨(⊥, ⊥), fha3) == true
# @test alphasat(⊥, ∨(⊥, α), fha3) == true
# @test alphasat(⊥, ∨(⊥, ⊤), fha3) == true
# @test alphasat(⊥, ∨(α, ⊥), fha3) == true
# @test alphasat(⊥, ∨(α, α), fha3) == true
# @test alphasat(⊥, ∨(α, ⊤), fha3) == true
# @test alphasat(⊥, ∨(⊤, ⊥), fha3) == true
# @test alphasat(⊥, ∨(⊤, α), fha3) == true
# @test alphasat(⊥, ∨(⊤, ⊤), fha3) == true
# @test alphasat(⊥, →(⊥, ⊥), fha3) == true
# @test alphasat(⊥, →(⊥, α), fha3) == true
# @test alphasat(⊥, →(⊥, ⊤), fha3) == true
# @test alphasat(⊥, →(α, ⊥), fha3) == true
# @test alphasat(⊥, →(α, α), fha3) == true
# @test alphasat(⊥, →(α, ⊤), fha3) == true
# @test alphasat(⊥, →(⊤, ⊥), fha3) == true
# @test alphasat(⊥, →(⊤, α), fha3) == true
# @test alphasat(⊥, →(⊤, ⊤), fha3) == true

# @test alphasat(α, ⊥,       fha3) == false
# @test alphasat(α, α,       fha3) == true
# @test alphasat(α, ⊤,       fha3) == true
# @test alphasat(α, ∧(⊥, ⊥), fha3) == false
# @test alphasat(α, ∧(⊥, α), fha3) == false
# @test alphasat(α, ∧(⊥, ⊤), fha3) == false
# @test alphasat(α, ∧(α, ⊥), fha3) == false
# @test alphasat(α, ∧(α, α), fha3) == true
# @test alphasat(α, ∧(α, ⊤), fha3) == true
# @test alphasat(α, ∧(⊤, ⊥), fha3) == false
# @test alphasat(α, ∧(⊤, α), fha3) == true
# @test alphasat(α, ∧(⊤, ⊤), fha3) == true
# @test alphasat(α, ∨(⊥, ⊥), fha3) == false
# @test alphasat(α, ∨(⊥, α), fha3) == true
# @test alphasat(α, ∨(⊥, ⊤), fha3) == true
# @test alphasat(α, ∨(α, ⊥), fha3) == true
# @test alphasat(α, ∨(α, α), fha3) == true
# @test alphasat(α, ∨(α, ⊤), fha3) == true
# @test alphasat(α, ∨(⊤, ⊥), fha3) == true
# @test alphasat(α, ∨(⊤, α), fha3) == true
# @test alphasat(α, ∨(⊤, ⊤), fha3) == true
# @test alphasat(α, →(⊥, ⊥), fha3) == true
# @test alphasat(α, →(⊥, α), fha3) == true
# @test alphasat(α, →(⊥, ⊤), fha3) == true
# @test alphasat(α, →(α, ⊥), fha3) == false
# @test alphasat(α, →(α, α), fha3) == true
# @test alphasat(α, →(α, ⊤), fha3) == true
# @test alphasat(α, →(⊤, ⊥), fha3) == false
# @test alphasat(α, →(⊤, α), fha3) == true
# @test alphasat(α, →(⊤, ⊤), fha3) == true

# @test alphasat(⊤, ⊥,       fha3) == false
# @test alphasat(⊤, α,       fha3) == false
# @test alphasat(⊤, ⊤,       fha3) == true
# @test alphasat(⊤, ∧(⊥, ⊥), fha3) == false
# @test alphasat(⊤, ∧(⊥, α), fha3) == false
# @test alphasat(⊤, ∧(⊥, ⊤), fha3) == false
# @test alphasat(⊤, ∧(α, ⊥), fha3) == false
# @test alphasat(⊤, ∧(α, α), fha3) == false
# @test alphasat(⊤, ∧(α, ⊤), fha3) == false
# @test alphasat(⊤, ∧(⊤, ⊥), fha3) == false
# @test alphasat(⊤, ∧(⊤, α), fha3) == false
# @test alphasat(⊤, ∧(⊤, ⊤), fha3) == true
# @test alphasat(⊤, ∨(⊥, ⊥), fha3) == false
# @test alphasat(⊤, ∨(⊥, α), fha3) == false
# @test alphasat(⊤, ∨(⊥, ⊤), fha3) == true
# @test alphasat(⊤, ∨(α, ⊥), fha3) == false
# @test alphasat(⊤, ∨(α, α), fha3) == false
# @test alphasat(⊤, ∨(α, ⊤), fha3) == true
# @test alphasat(⊤, ∨(⊤, ⊥), fha3) == true
# @test alphasat(⊤, ∨(⊤, α), fha3) == true
# @test alphasat(⊤, ∨(⊤, ⊤), fha3) == true
# @test alphasat(⊤, →(⊥, ⊥), fha3) == true
# @test alphasat(⊤, →(⊥, α), fha3) == true
# @test alphasat(⊤, →(⊥, ⊤), fha3) == true
# @test alphasat(⊤, →(α, ⊥), fha3) == true
# @test alphasat(⊤, →(α, α), fha3) == true
# @test alphasat(⊤, →(α, ⊤), fha3) == true
# @test alphasat(⊤, →(⊤, ⊥), fha3) == false
# @test alphasat(⊤, →(⊤, α), fha3) == false
# @test alphasat(⊤, →(⊤, ⊤), fha3) == true

# @test alphasat(
#     α,
#     →(
#         ∧(
#             →(
#                 α,
#                 Atom("A")
#             ),
#             →(
#                 ⊤,
#                 →(
#                     Atom("A"),
#                     Atom("B")
#                 )
#             )
#         ),
#         Atom("B")
#     ),
#     fha3
# ) == true

############################################################################################
#### Four-valued algebras ##################################################################
############################################################################################

α = FiniteTruth("α")
β = FiniteTruth("β")

d4 = Vector{FiniteTruth}([⊥, α, β, ⊤])

# a ∨ b = max{a, b}
jointable = Dict{Tuple{FiniteTruth, FiniteTruth}, FiniteTruth}(
    (⊥, ⊥) => ⊥, (⊥, α) => α, (⊥, β) => β, (⊥, ⊤) => ⊤,
    (α, ⊥) => α, (α, α) => α, (α, β) => β, (α, ⊤) => ⊤,
    (β, ⊥) => β, (β, α) => β, (β, β) => β, (β, ⊤) => ⊤,
    (⊤, ⊥) => ⊤, (⊤, α) => ⊤, (⊤, β) => ⊤, (⊤, ⊤) => ⊤
)

# a ∧ b = min{a, b}
meettable = Dict{Tuple{FiniteTruth, FiniteTruth}, FiniteTruth}(
    (⊥, ⊥) => ⊥, (⊥, α) => ⊥, (⊥, β) => ⊥, (⊥, ⊤) => ⊥,
    (α, ⊥) => ⊥, (α, α) => α, (α, β) => α, (α, ⊤) => α,
    (β, ⊥) => ⊥, (β, α) => α, (β, β) => β, (β, ⊤) => β,
    (⊤, ⊥) => ⊥, (⊤, α) => α, (⊤, β) => β, (⊤, ⊤) => ⊤
)

# a ⋅Ł b = max{0, a + b - 1}   
lnormtable = Dict{Tuple{FiniteTruth, FiniteTruth}, FiniteTruth}(
    (⊥, ⊥) => ⊥, (⊥, α) => ⊥, (⊥, β) => ⊥, (⊥, ⊤) => ⊥,
    (α, ⊥) => ⊥, (α, α) => ⊥, (α, β) => ⊥, (α, ⊤) => α,
    (β, ⊥) => ⊥, (β, α) => ⊥, (β, β) => α, (β, ⊤) => β,
    (⊤, ⊥) => ⊥, (⊤, α) => α, (⊤, β) => β, (⊤, ⊤) => ⊤
)

join = BinaryOperation(d4, jointable)
meet = BinaryOperation(d4, meettable)
lnorm = BinaryOperation(d4, lnormtable)

G4 = FiniteFLewAlgebra(join, meet, meet, ⊥, ⊤)
Ł4 = FiniteFLewAlgebra(join, meet, lnorm, ⊥, ⊤)

# println(G4)
# println(Ł4)

# G4 implication
# Implication: Dict{Tuple{FiniteTruth, FiniteTruth}, FiniteTruth}(
#     (⊤, α) => α, (β, ⊤) => ⊤, (⊤, β) => β, (β, β) => ⊤,
#     (⊥, α) => ⊤, (⊤, ⊥) => ⊥, (β, α) => α, (α, β) => ⊤,
#     (⊥, ⊥) => ⊤, (⊥, ⊤) => ⊤, (⊤, ⊤) => ⊤, (β, ⊥) => ⊥,
#     (α, ⊤) => ⊤, (α, α) => ⊤, (α, ⊥) => ⊥, (⊥, β) => ⊤
# )

# Ł4 implication
# Implication: Dict{Tuple{FiniteTruth, FiniteTruth}, FiniteTruth}(
#     (⊤, α) => α, (β, ⊤) => ⊤, (⊤, β) => β, (β, β) => ⊤,
#     (⊥, α) => ⊤, (⊤, ⊥) => ⊥, (β, α) => β, (α, β) => ⊤,
#     (⊥, ⊥) => ⊤, (⊥, ⊤) => ⊤, (⊤, ⊤) => ⊤, (β, ⊥) => α,
#     (α, ⊤) => ⊤, (α, α) => ⊤, (α, ⊥) => β, (⊥, β) => ⊤
# )

############################################################################################
#### G4 base cases #########################################################################
############################################################################################
@test alphasat(⊥, ⊥, G4) == true
@test alphasat(⊥, α, G4) == true
@test alphasat(⊥, β, G4) == true
@test alphasat(⊥, ⊤, G4) == true
@test alphasat(α, ⊥, G4) == false
@test alphasat(α, α, G4) == true
@test alphasat(α, β, G4) == true
@test alphasat(α, ⊤, G4) == true
@test alphasat(β, ⊥, G4) == false
@test alphasat(β, α, G4) == false
@test alphasat(β, β, G4) == true
@test alphasat(β, ⊤, G4) == true
@test alphasat(⊤, ⊥, G4) == false
@test alphasat(⊤, α, G4) == false
@test alphasat(⊤, β, G4) == false
@test alphasat(⊤, ⊤, G4) == true

############################################################################################
#### G4 join cases #########################################################################
############################################################################################
@test alphasat(⊥, ∨(⊥, ⊥), G4) == true
@test alphasat(⊥, ∨(⊥, α), G4) == true
@test alphasat(⊥, ∨(⊥, β), G4) == true
@test alphasat(⊥, ∨(⊥, ⊤), G4) == true
@test alphasat(⊥, ∨(α, ⊥), G4) == true
@test alphasat(⊥, ∨(α, α), G4) == true
@test alphasat(⊥, ∨(α, β), G4) == true
@test alphasat(⊥, ∨(α, ⊤), G4) == true
@test alphasat(⊥, ∨(β, ⊥), G4) == true
@test alphasat(⊥, ∨(β, α), G4) == true
@test alphasat(⊥, ∨(β, β), G4) == true
@test alphasat(⊥, ∨(β, ⊤), G4) == true
@test alphasat(⊥, ∨(⊤, ⊥), G4) == true
@test alphasat(⊥, ∨(⊤, α), G4) == true
@test alphasat(⊥, ∨(⊤, β), G4) == true
@test alphasat(⊥, ∨(⊤, ⊤), G4) == true

@test alphasat(α, ∨(⊥, ⊥), G4) == false
@test alphasat(α, ∨(⊥, α), G4) == true
@test alphasat(α, ∨(⊥, β), G4) == true
@test alphasat(α, ∨(⊥, ⊤), G4) == true
@test alphasat(α, ∨(α, ⊥), G4) == true
@test alphasat(α, ∨(α, α), G4) == true
@test alphasat(α, ∨(α, β), G4) == true
@test alphasat(α, ∨(α, ⊤), G4) == true
@test alphasat(α, ∨(β, ⊥), G4) == true
@test alphasat(α, ∨(β, α), G4) == true
@test alphasat(α, ∨(β, β), G4) == true
@test alphasat(α, ∨(β, ⊤), G4) == true
@test alphasat(α, ∨(⊤, ⊥), G4) == true
@test alphasat(α, ∨(⊤, α), G4) == true
@test alphasat(α, ∨(⊤, β), G4) == true
@test alphasat(α, ∨(⊤, ⊤), G4) == true

@test alphasat(β, ∨(⊥, ⊥), G4) == false
@test alphasat(β, ∨(⊥, α), G4) == false
@test alphasat(β, ∨(⊥, β), G4) == true
@test alphasat(β, ∨(⊥, ⊤), G4) == true
@test alphasat(β, ∨(α, ⊥), G4) == false
@test alphasat(β, ∨(α, α), G4) == false
@test alphasat(β, ∨(α, β), G4) == true
@test alphasat(β, ∨(α, ⊤), G4) == true
@test alphasat(β, ∨(β, ⊥), G4) == true
@test alphasat(β, ∨(β, α), G4) == true
@test alphasat(β, ∨(β, β), G4) == true
@test alphasat(β, ∨(β, ⊤), G4) == true
@test alphasat(β, ∨(⊤, ⊥), G4) == true
@test alphasat(β, ∨(⊤, α), G4) == true
@test alphasat(β, ∨(⊤, β), G4) == true
@test alphasat(β, ∨(⊤, ⊤), G4) == true

@test alphasat(⊤, ∨(⊥, ⊥), G4) == false
@test alphasat(⊤, ∨(⊥, α), G4) == false
@test alphasat(⊤, ∨(⊥, β), G4) == false
@test alphasat(⊤, ∨(⊥, ⊤), G4) == true
@test alphasat(⊤, ∨(α, ⊥), G4) == false
@test alphasat(⊤, ∨(α, α), G4) == false
@test alphasat(⊤, ∨(α, β), G4) == false
@test alphasat(⊤, ∨(α, ⊤), G4) == true
@test alphasat(⊤, ∨(β, ⊥), G4) == false
@test alphasat(⊤, ∨(β, α), G4) == false
@test alphasat(⊤, ∨(β, β), G4) == false
@test alphasat(⊤, ∨(β, ⊤), G4) == true
@test alphasat(⊤, ∨(⊤, ⊥), G4) == true
@test alphasat(⊤, ∨(⊤, α), G4) == true
@test alphasat(⊤, ∨(⊤, β), G4) == true
@test alphasat(⊤, ∨(⊤, ⊤), G4) == true

############################################################################################
#### G4 meet cases #########################################################################
############################################################################################
@test alphasat(⊥, ∧(⊥, ⊥), G4) == true
@test alphasat(⊥, ∧(⊥, α), G4) == true
@test alphasat(⊥, ∧(⊥, β), G4) == true
@test alphasat(⊥, ∧(⊥, ⊤), G4) == true
@test alphasat(⊥, ∧(α, ⊥), G4) == true
@test alphasat(⊥, ∧(α, α), G4) == true
@test alphasat(⊥, ∧(α, β), G4) == true
@test alphasat(⊥, ∧(α, ⊤), G4) == true
@test alphasat(⊥, ∧(β, ⊥), G4) == true
@test alphasat(⊥, ∧(β, α), G4) == true
@test alphasat(⊥, ∧(β, β), G4) == true
@test alphasat(⊥, ∧(β, ⊤), G4) == true
@test alphasat(⊥, ∧(⊤, ⊥), G4) == true
@test alphasat(⊥, ∧(⊤, α), G4) == true
@test alphasat(⊥, ∧(⊤, β), G4) == true
@test alphasat(⊥, ∧(⊤, ⊤), G4) == true

@test alphasat(α, ∧(⊥, ⊥), G4) == false
@test alphasat(α, ∧(⊥, α), G4) == false
@test alphasat(α, ∧(⊥, β), G4) == false
@test alphasat(α, ∧(⊥, ⊤), G4) == false
@test alphasat(α, ∧(α, ⊥), G4) == false
@test alphasat(α, ∧(α, α), G4) == true
@test alphasat(α, ∧(α, β), G4) == true
@test alphasat(α, ∧(α, ⊤), G4) == true
@test alphasat(α, ∧(β, ⊥), G4) == false
@test alphasat(α, ∧(β, α), G4) == true
@test alphasat(α, ∧(β, β), G4) == true
@test alphasat(α, ∧(β, ⊤), G4) == true
@test alphasat(α, ∧(⊤, ⊥), G4) == false
@test alphasat(α, ∧(⊤, α), G4) == true
@test alphasat(α, ∧(⊤, β), G4) == true
@test alphasat(α, ∧(⊤, ⊤), G4) == true

@test alphasat(β, ∧(⊥, ⊥), G4) == false
@test alphasat(β, ∧(⊥, α), G4) == false
@test alphasat(β, ∧(⊥, β), G4) == false
@test alphasat(β, ∧(⊥, ⊤), G4) == false
@test alphasat(β, ∧(α, ⊥), G4) == false
@test alphasat(β, ∧(α, α), G4) == false
@test alphasat(β, ∧(α, β), G4) == false
@test alphasat(β, ∧(α, ⊤), G4) == false
@test alphasat(β, ∧(β, ⊥), G4) == false
@test alphasat(β, ∧(β, α), G4) == false
@test alphasat(β, ∧(β, β), G4) == true
@test alphasat(β, ∧(β, ⊤), G4) == true
@test alphasat(β, ∧(⊤, ⊥), G4) == false
@test alphasat(β, ∧(⊤, α), G4) == false
@test alphasat(β, ∧(⊤, β), G4) == true
@test alphasat(β, ∧(⊤, ⊤), G4) == true

@test alphasat(⊤, ∧(⊥, ⊥), G4) == false
@test alphasat(⊤, ∧(⊥, α), G4) == false
@test alphasat(⊤, ∧(⊥, β), G4) == false
@test alphasat(⊤, ∧(⊥, ⊤), G4) == false
@test alphasat(⊤, ∧(α, ⊥), G4) == false
@test alphasat(⊤, ∧(α, α), G4) == false
@test alphasat(⊤, ∧(α, β), G4) == false
@test alphasat(⊤, ∧(α, ⊤), G4) == false
@test alphasat(⊤, ∧(β, ⊥), G4) == false
@test alphasat(⊤, ∧(β, α), G4) == false
@test alphasat(⊤, ∧(β, β), G4) == false
@test alphasat(⊤, ∧(β, ⊤), G4) == false
@test alphasat(⊤, ∧(⊤, ⊥), G4) == false
@test alphasat(⊤, ∧(⊤, α), G4) == false
@test alphasat(⊤, ∧(⊤, β), G4) == false
@test alphasat(⊤, ∧(⊤, ⊤), G4) == true

############################################################################################
#### G4 norm cases #########################################################################
############################################################################################
@test alphasat(⊥, ⋅(⊥, ⊥), G4) == true
@test alphasat(⊥, ⋅(⊥, α), G4) == true
@test alphasat(⊥, ⋅(⊥, β), G4) == true
@test alphasat(⊥, ⋅(⊥, ⊤), G4) == true
@test alphasat(⊥, ⋅(α, ⊥), G4) == true
@test alphasat(⊥, ⋅(α, α), G4) == true
@test alphasat(⊥, ⋅(α, β), G4) == true
@test alphasat(⊥, ⋅(α, ⊤), G4) == true
@test alphasat(⊥, ⋅(β, ⊥), G4) == true
@test alphasat(⊥, ⋅(β, α), G4) == true
@test alphasat(⊥, ⋅(β, β), G4) == true
@test alphasat(⊥, ⋅(β, ⊤), G4) == true
@test alphasat(⊥, ⋅(⊤, ⊥), G4) == true
@test alphasat(⊥, ⋅(⊤, α), G4) == true
@test alphasat(⊥, ⋅(⊤, β), G4) == true
@test alphasat(⊥, ⋅(⊤, ⊤), G4) == true

@test alphasat(α, ⋅(⊥, ⊥), G4) == false
@test alphasat(α, ⋅(⊥, α), G4) == false
@test alphasat(α, ⋅(⊥, β), G4) == false
@test alphasat(α, ⋅(⊥, ⊤), G4) == false
@test alphasat(α, ⋅(α, ⊥), G4) == false
@test alphasat(α, ⋅(α, α), G4) == true
@test alphasat(α, ⋅(α, β), G4) == true
@test alphasat(α, ⋅(α, ⊤), G4) == true
@test alphasat(α, ⋅(β, ⊥), G4) == false
@test alphasat(α, ⋅(β, α), G4) == true
@test alphasat(α, ⋅(β, β), G4) == true
@test alphasat(α, ⋅(β, ⊤), G4) == true
@test alphasat(α, ⋅(⊤, ⊥), G4) == false
@test alphasat(α, ⋅(⊤, α), G4) == true
@test alphasat(α, ⋅(⊤, β), G4) == true
@test alphasat(α, ⋅(⊤, ⊤), G4) == true

@test alphasat(β, ⋅(⊥, ⊥), G4) == false
@test alphasat(β, ⋅(⊥, α), G4) == false
@test alphasat(β, ⋅(⊥, β), G4) == false
@test alphasat(β, ⋅(⊥, ⊤), G4) == false
@test alphasat(β, ⋅(α, ⊥), G4) == false
@test alphasat(β, ⋅(α, α), G4) == false
@test alphasat(β, ⋅(α, β), G4) == false
@test alphasat(β, ⋅(α, ⊤), G4) == false
@test alphasat(β, ⋅(β, ⊥), G4) == false
@test alphasat(β, ⋅(β, α), G4) == false
@test alphasat(β, ⋅(β, β), G4) == true
@test alphasat(β, ⋅(β, ⊤), G4) == true
@test alphasat(β, ⋅(⊤, ⊥), G4) == false
@test alphasat(β, ⋅(⊤, α), G4) == false
@test alphasat(β, ⋅(⊤, β), G4) == true
@test alphasat(β, ⋅(⊤, ⊤), G4) == true

@test alphasat(⊤, ⋅(⊥, ⊥), G4) == false
@test alphasat(⊤, ⋅(⊥, α), G4) == false
@test alphasat(⊤, ⋅(⊥, β), G4) == false
@test alphasat(⊤, ⋅(⊥, ⊤), G4) == false
@test alphasat(⊤, ⋅(α, ⊥), G4) == false
@test alphasat(⊤, ⋅(α, α), G4) == false
@test alphasat(⊤, ⋅(α, β), G4) == false
@test alphasat(⊤, ⋅(α, ⊤), G4) == false
@test alphasat(⊤, ⋅(β, ⊥), G4) == false
@test alphasat(⊤, ⋅(β, α), G4) == false
@test alphasat(⊤, ⋅(β, β), G4) == false
@test alphasat(⊤, ⋅(β, ⊤), G4) == false
@test alphasat(⊤, ⋅(⊤, ⊥), G4) == false
@test alphasat(⊤, ⋅(⊤, α), G4) == false
@test alphasat(⊤, ⋅(⊤, β), G4) == false
@test alphasat(⊤, ⋅(⊤, ⊤), G4) == true

############################################################################################
#### G4 implication cases ##################################################################
############################################################################################
@test alphasat(⊥, →(⊥, ⊥), G4) == true
@test alphasat(⊥, →(⊥, α), G4) == true
@test alphasat(⊥, →(⊥, β), G4) == true
@test alphasat(⊥, →(⊥, ⊤), G4) == true
@test alphasat(⊥, →(α, ⊥), G4) == true
@test alphasat(⊥, →(α, α), G4) == true
@test alphasat(⊥, →(α, β), G4) == true
@test alphasat(⊥, →(α, ⊤), G4) == true
@test alphasat(⊥, →(β, ⊥), G4) == true
@test alphasat(⊥, →(β, α), G4) == true
@test alphasat(⊥, →(β, β), G4) == true
@test alphasat(⊥, →(β, ⊤), G4) == true
@test alphasat(⊥, →(⊤, ⊥), G4) == true
@test alphasat(⊥, →(⊤, α), G4) == true
@test alphasat(⊥, →(⊤, β), G4) == true
@test alphasat(⊥, →(⊤, ⊤), G4) == true

@test alphasat(α, →(⊥, ⊥), G4) == true
@test alphasat(α, →(⊥, α), G4) == true
@test alphasat(α, →(⊥, β), G4) == true
@test alphasat(α, →(⊥, ⊤), G4) == true
@test alphasat(α, →(α, ⊥), G4) == false
@test alphasat(α, →(α, α), G4) == true
@test alphasat(α, →(α, β), G4) == true
@test alphasat(α, →(α, ⊤), G4) == true
@test alphasat(α, →(β, ⊥), G4) == false
@test alphasat(α, →(β, α), G4) == true
@test alphasat(α, →(β, β), G4) == true
@test alphasat(α, →(β, ⊤), G4) == true
@test alphasat(α, →(⊤, ⊥), G4) == false
@test alphasat(α, →(⊤, α), G4) == true
@test alphasat(α, →(⊤, β), G4) == true
@test alphasat(α, →(⊤, ⊤), G4) == true

@test alphasat(β, →(⊥, ⊥), G4) == true
@test alphasat(β, →(⊥, α), G4) == true
@test alphasat(β, →(⊥, β), G4) == true
@test alphasat(β, →(⊥, ⊤), G4) == true
@test alphasat(β, →(α, ⊥), G4) == false
@test alphasat(β, →(α, α), G4) == true
@test alphasat(β, →(α, β), G4) == true
@test alphasat(β, →(α, ⊤), G4) == true
@test alphasat(β, →(β, ⊥), G4) == false
@test alphasat(β, →(β, α), G4) == false
@test alphasat(β, →(β, β), G4) == true
@test alphasat(β, →(β, ⊤), G4) == true
@test alphasat(β, →(⊤, ⊥), G4) == false
@test alphasat(β, →(⊤, α), G4) == false
@test alphasat(β, →(⊤, β), G4) == true
@test alphasat(β, →(⊤, ⊤), G4) == true

@test alphasat(⊤, →(⊥, ⊥), G4) == true
@test alphasat(⊤, →(⊥, α), G4) == true
@test alphasat(⊤, →(⊥, β), G4) == true
@test alphasat(⊤, →(⊥, ⊤), G4) == true
@test alphasat(⊤, →(α, ⊥), G4) == false
@test alphasat(⊤, →(α, α), G4) == true
@test alphasat(⊤, →(α, β), G4) == true
@test alphasat(⊤, →(α, ⊤), G4) == true
@test alphasat(⊤, →(β, ⊥), G4) == false
@test alphasat(⊤, →(β, α), G4) == false
@test alphasat(⊤, →(β, β), G4) == true
@test alphasat(⊤, →(β, ⊤), G4) == true
@test alphasat(⊤, →(⊤, ⊥), G4) == false
@test alphasat(⊤, →(⊤, α), G4) == false
@test alphasat(⊤, →(⊤, β), G4) == false
@test alphasat(⊤, →(⊤, ⊤), G4) == true

############################################################################################
#### Ł4 base cases #########################################################################
############################################################################################
@test alphasat(⊥, ⊥, Ł4) == true
@test alphasat(⊥, α, Ł4) == true
@test alphasat(⊥, β, Ł4) == true
@test alphasat(⊥, ⊤, Ł4) == true
@test alphasat(α, ⊥, Ł4) == false
@test alphasat(α, α, Ł4) == true
@test alphasat(α, β, Ł4) == true
@test alphasat(α, ⊤, Ł4) == true
@test alphasat(β, ⊥, Ł4) == false
@test alphasat(β, α, Ł4) == false
@test alphasat(β, β, Ł4) == true
@test alphasat(β, ⊤, Ł4) == true
@test alphasat(⊤, ⊥, Ł4) == false
@test alphasat(⊤, α, Ł4) == false
@test alphasat(⊤, β, Ł4) == false
@test alphasat(⊤, ⊤, Ł4) == true

############################################################################################
#### Ł4 join cases #########################################################################
############################################################################################
@test alphasat(⊥, ∨(⊥, ⊥), Ł4) == true
@test alphasat(⊥, ∨(⊥, α), Ł4) == true
@test alphasat(⊥, ∨(⊥, β), Ł4) == true
@test alphasat(⊥, ∨(⊥, ⊤), Ł4) == true
@test alphasat(⊥, ∨(α, ⊥), Ł4) == true
@test alphasat(⊥, ∨(α, α), Ł4) == true
@test alphasat(⊥, ∨(α, β), Ł4) == true
@test alphasat(⊥, ∨(α, ⊤), Ł4) == true
@test alphasat(⊥, ∨(β, ⊥), Ł4) == true
@test alphasat(⊥, ∨(β, α), Ł4) == true
@test alphasat(⊥, ∨(β, β), Ł4) == true
@test alphasat(⊥, ∨(β, ⊤), Ł4) == true
@test alphasat(⊥, ∨(⊤, ⊥), Ł4) == true
@test alphasat(⊥, ∨(⊤, α), Ł4) == true
@test alphasat(⊥, ∨(⊤, β), Ł4) == true
@test alphasat(⊥, ∨(⊤, ⊤), Ł4) == true

@test alphasat(α, ∨(⊥, ⊥), Ł4) == false
@test alphasat(α, ∨(⊥, α), Ł4) == true
@test alphasat(α, ∨(⊥, β), Ł4) == true
@test alphasat(α, ∨(⊥, ⊤), Ł4) == true
@test alphasat(α, ∨(α, ⊥), Ł4) == true
@test alphasat(α, ∨(α, α), Ł4) == true
@test alphasat(α, ∨(α, β), Ł4) == true
@test alphasat(α, ∨(α, ⊤), Ł4) == true
@test alphasat(α, ∨(β, ⊥), Ł4) == true
@test alphasat(α, ∨(β, α), Ł4) == true
@test alphasat(α, ∨(β, β), Ł4) == true
@test alphasat(α, ∨(β, ⊤), Ł4) == true
@test alphasat(α, ∨(⊤, ⊥), Ł4) == true
@test alphasat(α, ∨(⊤, α), Ł4) == true
@test alphasat(α, ∨(⊤, β), Ł4) == true
@test alphasat(α, ∨(⊤, ⊤), Ł4) == true

@test alphasat(β, ∨(⊥, ⊥), Ł4) == false
@test alphasat(β, ∨(⊥, α), Ł4) == false
@test alphasat(β, ∨(⊥, β), Ł4) == true
@test alphasat(β, ∨(⊥, ⊤), Ł4) == true
@test alphasat(β, ∨(α, ⊥), Ł4) == false
@test alphasat(β, ∨(α, α), Ł4) == false
@test alphasat(β, ∨(α, β), Ł4) == true
@test alphasat(β, ∨(α, ⊤), Ł4) == true
@test alphasat(β, ∨(β, ⊥), Ł4) == true
@test alphasat(β, ∨(β, α), Ł4) == true
@test alphasat(β, ∨(β, β), Ł4) == true
@test alphasat(β, ∨(β, ⊤), Ł4) == true
@test alphasat(β, ∨(⊤, ⊥), Ł4) == true
@test alphasat(β, ∨(⊤, α), Ł4) == true
@test alphasat(β, ∨(⊤, β), Ł4) == true
@test alphasat(β, ∨(⊤, ⊤), Ł4) == true

@test alphasat(⊤, ∨(⊥, ⊥), Ł4) == false
@test alphasat(⊤, ∨(⊥, α), Ł4) == false
@test alphasat(⊤, ∨(⊥, β), Ł4) == false
@test alphasat(⊤, ∨(⊥, ⊤), Ł4) == true
@test alphasat(⊤, ∨(α, ⊥), Ł4) == false
@test alphasat(⊤, ∨(α, α), Ł4) == false
@test alphasat(⊤, ∨(α, β), Ł4) == false
@test alphasat(⊤, ∨(α, ⊤), Ł4) == true
@test alphasat(⊤, ∨(β, ⊥), Ł4) == false
@test alphasat(⊤, ∨(β, α), Ł4) == false
@test alphasat(⊤, ∨(β, β), Ł4) == false
@test alphasat(⊤, ∨(β, ⊤), Ł4) == true
@test alphasat(⊤, ∨(⊤, ⊥), Ł4) == true
@test alphasat(⊤, ∨(⊤, α), Ł4) == true
@test alphasat(⊤, ∨(⊤, β), Ł4) == true
@test alphasat(⊤, ∨(⊤, ⊤), Ł4) == true

############################################################################################
#### Ł4 meet cases #########################################################################
############################################################################################
@test alphasat(⊥, ∧(⊥, ⊥), Ł4) == true
@test alphasat(⊥, ∧(⊥, α), Ł4) == true
@test alphasat(⊥, ∧(⊥, β), Ł4) == true
@test alphasat(⊥, ∧(⊥, ⊤), Ł4) == true
@test alphasat(⊥, ∧(α, ⊥), Ł4) == true
@test alphasat(⊥, ∧(α, α), Ł4) == true
@test alphasat(⊥, ∧(α, β), Ł4) == true
@test alphasat(⊥, ∧(α, ⊤), Ł4) == true
@test alphasat(⊥, ∧(β, ⊥), Ł4) == true
@test alphasat(⊥, ∧(β, α), Ł4) == true
@test alphasat(⊥, ∧(β, β), Ł4) == true
@test alphasat(⊥, ∧(β, ⊤), Ł4) == true
@test alphasat(⊥, ∧(⊤, ⊥), Ł4) == true
@test alphasat(⊥, ∧(⊤, α), Ł4) == true
@test alphasat(⊥, ∧(⊤, β), Ł4) == true
@test alphasat(⊥, ∧(⊤, ⊤), Ł4) == true

@test alphasat(α, ∧(⊥, ⊥), Ł4) == false
@test alphasat(α, ∧(⊥, α), Ł4) == false
@test alphasat(α, ∧(⊥, β), Ł4) == false
@test alphasat(α, ∧(⊥, ⊤), Ł4) == false
@test alphasat(α, ∧(α, ⊥), Ł4) == false
@test alphasat(α, ∧(α, α), Ł4) == true
@test alphasat(α, ∧(α, β), Ł4) == true
@test alphasat(α, ∧(α, ⊤), Ł4) == true
@test alphasat(α, ∧(β, ⊥), Ł4) == false
@test alphasat(α, ∧(β, α), Ł4) == true
@test alphasat(α, ∧(β, β), Ł4) == true
@test alphasat(α, ∧(β, ⊤), Ł4) == true
@test alphasat(α, ∧(⊤, ⊥), Ł4) == false
@test alphasat(α, ∧(⊤, α), Ł4) == true
@test alphasat(α, ∧(⊤, β), Ł4) == true
@test alphasat(α, ∧(⊤, ⊤), Ł4) == true

@test alphasat(β, ∧(⊥, ⊥), Ł4) == false
@test alphasat(β, ∧(⊥, α), Ł4) == false
@test alphasat(β, ∧(⊥, β), Ł4) == false
@test alphasat(β, ∧(⊥, ⊤), Ł4) == false
@test alphasat(β, ∧(α, ⊥), Ł4) == false
@test alphasat(β, ∧(α, α), Ł4) == false
@test alphasat(β, ∧(α, β), Ł4) == false
@test alphasat(β, ∧(α, ⊤), Ł4) == false
@test alphasat(β, ∧(β, ⊥), Ł4) == false
@test alphasat(β, ∧(β, α), Ł4) == false
@test alphasat(β, ∧(β, β), Ł4) == true
@test alphasat(β, ∧(β, ⊤), Ł4) == true
@test alphasat(β, ∧(⊤, ⊥), Ł4) == false
@test alphasat(β, ∧(⊤, α), Ł4) == false
@test alphasat(β, ∧(⊤, β), Ł4) == true
@test alphasat(β, ∧(⊤, ⊤), Ł4) == true

@test alphasat(⊤, ∧(⊥, ⊥), Ł4) == false
@test alphasat(⊤, ∧(⊥, α), Ł4) == false
@test alphasat(⊤, ∧(⊥, β), Ł4) == false
@test alphasat(⊤, ∧(⊥, ⊤), Ł4) == false
@test alphasat(⊤, ∧(α, ⊥), Ł4) == false
@test alphasat(⊤, ∧(α, α), Ł4) == false
@test alphasat(⊤, ∧(α, β), Ł4) == false
@test alphasat(⊤, ∧(α, ⊤), Ł4) == false
@test alphasat(⊤, ∧(β, ⊥), Ł4) == false
@test alphasat(⊤, ∧(β, α), Ł4) == false
@test alphasat(⊤, ∧(β, β), Ł4) == false
@test alphasat(⊤, ∧(β, ⊤), Ł4) == false
@test alphasat(⊤, ∧(⊤, ⊥), Ł4) == false
@test alphasat(⊤, ∧(⊤, α), Ł4) == false
@test alphasat(⊤, ∧(⊤, β), Ł4) == false
@test alphasat(⊤, ∧(⊤, ⊤), Ł4) == true

############################################################################################
#### Ł4 norm cases #########################################################################
############################################################################################
@test alphasat(⊥, ⋅(⊥, ⊥), Ł4) == true
@test alphasat(⊥, ⋅(⊥, α), Ł4) == true
@test alphasat(⊥, ⋅(⊥, β), Ł4) == true
@test alphasat(⊥, ⋅(⊥, ⊤), Ł4) == true
@test alphasat(⊥, ⋅(α, ⊥), Ł4) == true
@test alphasat(⊥, ⋅(α, α), Ł4) == true
@test alphasat(⊥, ⋅(α, β), Ł4) == true
@test alphasat(⊥, ⋅(α, ⊤), Ł4) == true
@test alphasat(⊥, ⋅(β, ⊥), Ł4) == true
@test alphasat(⊥, ⋅(β, α), Ł4) == true
@test alphasat(⊥, ⋅(β, β), Ł4) == true
@test alphasat(⊥, ⋅(β, ⊤), Ł4) == true
@test alphasat(⊥, ⋅(⊤, ⊥), Ł4) == true
@test alphasat(⊥, ⋅(⊤, α), Ł4) == true
@test alphasat(⊥, ⋅(⊤, β), Ł4) == true
@test alphasat(⊥, ⋅(⊤, ⊤), Ł4) == true

@test alphasat(α, ⋅(⊥, ⊥), Ł4) == false
@test alphasat(α, ⋅(⊥, α), Ł4) == false
@test alphasat(α, ⋅(⊥, β), Ł4) == false
@test alphasat(α, ⋅(⊥, ⊤), Ł4) == false
@test alphasat(α, ⋅(α, ⊥), Ł4) == false
@test alphasat(α, ⋅(α, α), Ł4) == false
@test alphasat(α, ⋅(α, β), Ł4) == false
@test alphasat(α, ⋅(α, ⊤), Ł4) == true
@test alphasat(α, ⋅(β, ⊥), Ł4) == false
@test alphasat(α, ⋅(β, α), Ł4) == false
@test alphasat(α, ⋅(β, β), Ł4) == true
@test alphasat(α, ⋅(β, ⊤), Ł4) == true
@test alphasat(α, ⋅(⊤, ⊥), Ł4) == false
@test alphasat(α, ⋅(⊤, α), Ł4) == true
@test alphasat(α, ⋅(⊤, β), Ł4) == true
@test alphasat(α, ⋅(⊤, ⊤), Ł4) == true

@test alphasat(β, ⋅(⊥, ⊥), Ł4) == false
@test alphasat(β, ⋅(⊥, α), Ł4) == false
@test alphasat(β, ⋅(⊥, β), Ł4) == false
@test alphasat(β, ⋅(⊥, ⊤), Ł4) == false
@test alphasat(β, ⋅(α, ⊥), Ł4) == false
@test alphasat(β, ⋅(α, α), Ł4) == false
@test alphasat(β, ⋅(α, β), Ł4) == false
@test alphasat(β, ⋅(α, ⊤), Ł4) == false
@test alphasat(β, ⋅(β, ⊥), Ł4) == false
@test alphasat(β, ⋅(β, α), Ł4) == false
@test alphasat(β, ⋅(β, β), Ł4) == false
@test alphasat(β, ⋅(β, ⊤), Ł4) == true
@test alphasat(β, ⋅(⊤, ⊥), Ł4) == false
@test alphasat(β, ⋅(⊤, α), Ł4) == false
@test alphasat(β, ⋅(⊤, β), Ł4) == true
@test alphasat(β, ⋅(⊤, ⊤), Ł4) == true

@test alphasat(⊤, ⋅(⊥, ⊥), Ł4) == false
@test alphasat(⊤, ⋅(⊥, α), Ł4) == false
@test alphasat(⊤, ⋅(⊥, β), Ł4) == false
@test alphasat(⊤, ⋅(⊥, ⊤), Ł4) == false
@test alphasat(⊤, ⋅(α, ⊥), Ł4) == false
@test alphasat(⊤, ⋅(α, α), Ł4) == false
@test alphasat(⊤, ⋅(α, β), Ł4) == false
@test alphasat(⊤, ⋅(α, ⊤), Ł4) == false
@test alphasat(⊤, ⋅(β, ⊥), Ł4) == false
@test alphasat(⊤, ⋅(β, α), Ł4) == false
@test alphasat(⊤, ⋅(β, β), Ł4) == false
@test alphasat(⊤, ⋅(β, ⊤), Ł4) == false
@test alphasat(⊤, ⋅(⊤, ⊥), Ł4) == false
@test alphasat(⊤, ⋅(⊤, α), Ł4) == false
@test alphasat(⊤, ⋅(⊤, β), Ł4) == false
@test alphasat(⊤, ⋅(⊤, ⊤), Ł4) == true

############################################################################################
#### Ł4 implication cases ##################################################################
############################################################################################
@test alphasat(⊥, →(⊥, ⊥), Ł4) == true
@test alphasat(⊥, →(⊥, α), Ł4) == true
@test alphasat(⊥, →(⊥, β), Ł4) == true
@test alphasat(⊥, →(⊥, ⊤), Ł4) == true
@test alphasat(⊥, →(α, ⊥), Ł4) == true
@test alphasat(⊥, →(α, α), Ł4) == true
@test alphasat(⊥, →(α, β), Ł4) == true
@test alphasat(⊥, →(α, ⊤), Ł4) == true
@test alphasat(⊥, →(β, ⊥), Ł4) == true
@test alphasat(⊥, →(β, α), Ł4) == true
@test alphasat(⊥, →(β, β), Ł4) == true
@test alphasat(⊥, →(β, ⊤), Ł4) == true
@test alphasat(⊥, →(⊤, ⊥), Ł4) == true
@test alphasat(⊥, →(⊤, α), Ł4) == true
@test alphasat(⊥, →(⊤, β), Ł4) == true
@test alphasat(⊥, →(⊤, ⊤), Ł4) == true

@test alphasat(α, →(⊥, ⊥), Ł4) == true
@test alphasat(α, →(⊥, α), Ł4) == true
@test alphasat(α, →(⊥, β), Ł4) == true
@test alphasat(α, →(⊥, ⊤), Ł4) == true
@test alphasat(α, →(α, ⊥), Ł4) == true
@test alphasat(α, →(α, α), Ł4) == true
@test alphasat(α, →(α, β), Ł4) == true
@test alphasat(α, →(α, ⊤), Ł4) == true
@test alphasat(α, →(β, ⊥), Ł4) == true
@test alphasat(α, →(β, α), Ł4) == true
@test alphasat(α, →(β, β), Ł4) == true
@test alphasat(α, →(β, ⊤), Ł4) == true
@test alphasat(α, →(⊤, ⊥), Ł4) == false
@test alphasat(α, →(⊤, α), Ł4) == true
@test alphasat(α, →(⊤, β), Ł4) == true
@test alphasat(α, →(⊤, ⊤), Ł4) == true

@test alphasat(β, →(⊥, ⊥), Ł4) == true
@test alphasat(β, →(⊥, α), Ł4) == true
@test alphasat(β, →(⊥, β), Ł4) == true
@test alphasat(β, →(⊥, ⊤), Ł4) == true
@test alphasat(β, →(α, ⊥), Ł4) == true
@test alphasat(β, →(α, α), Ł4) == true
@test alphasat(β, →(α, β), Ł4) == true
@test alphasat(β, →(α, ⊤), Ł4) == true
@test alphasat(β, →(β, ⊥), Ł4) == false
@test alphasat(β, →(β, α), Ł4) == true
@test alphasat(β, →(β, β), Ł4) == true
@test alphasat(β, →(β, ⊤), Ł4) == true
@test alphasat(β, →(⊤, ⊥), Ł4) == false
@test alphasat(β, →(⊤, α), Ł4) == false
@test alphasat(β, →(⊤, β), Ł4) == true
@test alphasat(β, →(⊤, ⊤), Ł4) == true

@test alphasat(⊤, →(⊥, ⊥), Ł4) == true
@test alphasat(⊤, →(⊥, α), Ł4) == true
@test alphasat(⊤, →(⊥, β), Ł4) == true
@test alphasat(⊤, →(⊥, ⊤), Ł4) == true
@test alphasat(⊤, →(α, ⊥), Ł4) == false
@test alphasat(⊤, →(α, α), Ł4) == true
@test alphasat(⊤, →(α, β), Ł4) == true
@test alphasat(⊤, →(α, ⊤), Ł4) == true
@test alphasat(⊤, →(β, ⊥), Ł4) == false
@test alphasat(⊤, →(β, α), Ł4) == false
@test alphasat(⊤, →(β, β), Ł4) == true
@test alphasat(⊤, →(β, ⊤), Ł4) == true
@test alphasat(⊤, →(⊤, ⊥), Ł4) == false
@test alphasat(⊤, →(⊤, α), Ł4) == false
@test alphasat(⊤, →(⊤, β), Ł4) == false
@test alphasat(⊤, →(⊤, ⊤), Ł4) == true
