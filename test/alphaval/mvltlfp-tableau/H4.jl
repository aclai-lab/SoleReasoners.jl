################################################################################
#### H4 ########################################################################
################################################################################

using SoleLogics.ManyValuedLogics: H4, getdomain
using SoleLogics.ManyValuedLogics: α, β

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

timeout = 60

################################################################################
## Base cases ##################################################################
################################################################################

for i ∈ getdomain(H4)
    for j ∈ getdomain(H4)
        @test alphaval(
            MVLTLFPTableau,
            i,
            j,
        H4) == alphasat(MVLTLFPTableau, i, j, H4)
        for k ∈ getdomain(H4)
            @test alphaval(
                MVLTLFPTableau,
                i,
                ∨(j,k),
                H4
            ) == alphasat(MVLTLFPTableau, i, ∨(j,k), H4)
            @test alphaval(
                MVLTLFPTableau,
                i,
                ∧(j,k),
                H4
            ) == alphasat(MVLTLFPTableau, i, ∧(j,k), H4)
            @test alphaval(
                MVLTLFPTableau,
                i,
                →(j,k),
                H4
            ) == alphasat(MVLTLFPTableau, i, →(j,k), H4)
        end
    end
end

@test alphaval(MVLTLFPTableau, ⊥, p, H4) == true
@test alphaval(MVLTLFPTableau, α, p, H4) == false
@test alphaval(MVLTLFPTableau, β, p, H4) == false
@test alphaval(MVLTLFPTableau, ⊤, p, H4) == false

################################################################################
## (Strong) disjuction #########################################################
################################################################################

@test alphaval(MVLTLFPTableau, ⊥, ∨(p, ⊥), H4) == true
@test alphaval(MVLTLFPTableau, ⊥, ∨(p, α), H4) == true
@test alphaval(MVLTLFPTableau, ⊥, ∨(p, β), H4) == true
@test alphaval(MVLTLFPTableau, ⊥, ∨(p, ⊤), H4) == true
@test alphaval(MVLTLFPTableau, α, ∨(p, ⊥), H4) == false
@test alphaval(MVLTLFPTableau, α, ∨(p, α), H4) == true
@test alphaval(MVLTLFPTableau, α, ∨(p, β), H4) == false
@test alphaval(MVLTLFPTableau, α, ∨(p, ⊤), H4) == true
@test alphaval(MVLTLFPTableau, β, ∨(p, ⊥), H4) == false
@test alphaval(MVLTLFPTableau, β, ∨(p, α), H4) == false
@test alphaval(MVLTLFPTableau, β, ∨(p, β), H4) == true
@test alphaval(MVLTLFPTableau, β, ∨(p, ⊤), H4) == true
@test alphaval(MVLTLFPTableau, ⊤, ∨(p, ⊥), H4) == false
@test alphaval(MVLTLFPTableau, ⊤, ∨(p, α), H4) == false
@test alphaval(MVLTLFPTableau, ⊤, ∨(p, β), H4) == false
@test alphaval(MVLTLFPTableau, ⊤, ∨(p, ⊤), H4) == true

@test alphaval(MVLTLFPTableau, ⊥, ∨(⊥, p), H4) == true 
@test alphaval(MVLTLFPTableau, ⊥, ∨(α, p), H4) == true 
@test alphaval(MVLTLFPTableau, ⊥, ∨(β, p), H4) == true 
@test alphaval(MVLTLFPTableau, ⊥, ∨(⊤, p), H4) == true 
@test alphaval(MVLTLFPTableau, α, ∨(⊥, p), H4) == false
@test alphaval(MVLTLFPTableau, α, ∨(α, p), H4) == true 
@test alphaval(MVLTLFPTableau, α, ∨(β, p), H4) == false 
@test alphaval(MVLTLFPTableau, α, ∨(⊤, p), H4) == true 
@test alphaval(MVLTLFPTableau, β, ∨(⊥, p), H4) == false 
@test alphaval(MVLTLFPTableau, β, ∨(α, p), H4) == false 
@test alphaval(MVLTLFPTableau, β, ∨(β, p), H4) == true 
@test alphaval(MVLTLFPTableau, β, ∨(⊤, p), H4) == true 
@test alphaval(MVLTLFPTableau, ⊤, ∨(⊥, p), H4) == false 
@test alphaval(MVLTLFPTableau, ⊤, ∨(α, p), H4) == false 
@test alphaval(MVLTLFPTableau, ⊤, ∨(β, p), H4) == false 
@test alphaval(MVLTLFPTableau, ⊤, ∨(⊤, p), H4) == true 

@test alphaval(
    MVLTLFPTableau,
    ⊥,
    ∨(p, p),
    H4
) == true
@test alphaval(
    MVLTLFPTableau,
    α,
    ∨(p, p),
    H4
) == false
@test alphaval(
    MVLTLFPTableau,
    β,
    ∨(p, p),
    H4
) == false
@test alphaval(
    MVLTLFPTableau,
    ⊤,
    ∨(p, p),
    H4
) == false

@test alphaval(
    MVLTLFPTableau,
    ⊥,
    ∨(p, q),
    H4
) == true
@test alphaval(
    MVLTLFPTableau,
    α,
    ∨(p, q),
    H4
) == false
@test alphaval(
    MVLTLFPTableau,
    β,
    ∨(p, q),
    H4
) == false
@test alphaval(
    MVLTLFPTableau,
    ⊤,
    ∨(p, q),
    H4
) == false

@test alphaval(
    MVLTLFPTableau,
    ⊥,
    ∨(q, p),
    H4
) == true
@test alphaval(
    MVLTLFPTableau,
    α,
    ∨(q, p),
    H4
) == false
@test alphaval(
    MVLTLFPTableau,
    β,
    ∨(q, p),
    H4
) == false
@test alphaval(
    MVLTLFPTableau,
    ⊤,
    ∨(q, p),
    H4
) == false

################################################################################
## (Strong) conjunction ########################################################
################################################################################

@test alphaval(MVLTLFPTableau, ⊥, ∧(p, ⊥), H4) == true
@test alphaval(MVLTLFPTableau, ⊥, ∧(p, α), H4) == true
@test alphaval(MVLTLFPTableau, ⊥, ∧(p, β), H4) == true
@test alphaval(MVLTLFPTableau, ⊥, ∧(p, ⊤), H4) == true
@test alphaval(MVLTLFPTableau, α, ∧(p, ⊥), H4) == false
@test alphaval(MVLTLFPTableau, α, ∧(p, α), H4) == false
@test alphaval(MVLTLFPTableau, α, ∧(p, β), H4) == false
@test alphaval(MVLTLFPTableau, α, ∧(p, ⊤), H4) == false
@test alphaval(MVLTLFPTableau, β, ∧(p, ⊥), H4) == false
@test alphaval(MVLTLFPTableau, β, ∧(p, α), H4) == false
@test alphaval(MVLTLFPTableau, β, ∧(p, β), H4) == false
@test alphaval(MVLTLFPTableau, β, ∧(p, ⊤), H4) == false
@test alphaval(MVLTLFPTableau, ⊤, ∧(p, ⊥), H4) == false
@test alphaval(MVLTLFPTableau, ⊤, ∧(p, α), H4) == false
@test alphaval(MVLTLFPTableau, ⊤, ∧(p, β), H4) == false
@test alphaval(MVLTLFPTableau, ⊤, ∧(p, ⊤), H4) == false

@test alphaval(MVLTLFPTableau, ⊥, ∧(⊥, p), H4) == true 
@test alphaval(MVLTLFPTableau, ⊥, ∧(α, p), H4) == true 
@test alphaval(MVLTLFPTableau, ⊥, ∧(β, p), H4) == true 
@test alphaval(MVLTLFPTableau, ⊥, ∧(⊤, p), H4) == true 
@test alphaval(MVLTLFPTableau, α, ∧(⊥, p), H4) == false
@test alphaval(MVLTLFPTableau, α, ∧(α, p), H4) == false 
@test alphaval(MVLTLFPTableau, α, ∧(β, p), H4) == false 
@test alphaval(MVLTLFPTableau, α, ∧(⊤, p), H4) == false 
@test alphaval(MVLTLFPTableau, β, ∧(⊥, p), H4) == false 
@test alphaval(MVLTLFPTableau, β, ∧(α, p), H4) == false 
@test alphaval(MVLTLFPTableau, β, ∧(β, p), H4) == false 
@test alphaval(MVLTLFPTableau, β, ∧(⊤, p), H4) == false 
@test alphaval(MVLTLFPTableau, ⊤, ∧(⊥, p), H4) == false 
@test alphaval(MVLTLFPTableau, ⊤, ∧(α, p), H4) == false 
@test alphaval(MVLTLFPTableau, ⊤, ∧(β, p), H4) == false 
@test alphaval(MVLTLFPTableau, ⊤, ∧(⊤, p), H4) == false 

@test alphaval(
    MVLTLFPTableau,
    ⊥,
    ∧(p, p),
    H4
) == true
@test alphaval(
    MVLTLFPTableau,
    α,
    ∧(p, p),
    H4
) == false
@test alphaval(
    MVLTLFPTableau,
    β,
    ∧(p, p),
    H4
) == false
@test alphaval(
    MVLTLFPTableau,
    ⊤,
    ∧(p, p),
    H4
) == false

@test alphaval(
    MVLTLFPTableau,
    ⊥,
    ∧(p, q),
    H4
) == true
@test alphaval(
    MVLTLFPTableau,
    α,
    ∧(p, q),
    H4
) == false
@test alphaval(
    MVLTLFPTableau,
    β,
    ∧(p, q),
    H4
) == false
@test alphaval(
    MVLTLFPTableau,
    ⊤,
    ∧(p, q),
    H4
) == false

@test alphaval(
    MVLTLFPTableau,
    ⊥,
    ∧(q, p),
    H4
) == true
@test alphaval(
    MVLTLFPTableau,
    α,
    ∧(q, p),
    H4
) == false
@test alphaval(
    MVLTLFPTableau,
    β,
    ∧(q, p),
    H4
) == false
@test alphaval(
    MVLTLFPTableau,
    ⊤,
    ∧(q, p),
    H4
) == false

################################################################################
## Implication #################################################################
################################################################################

@test alphaval(MVLTLFPTableau, ⊥, →(p, ⊥), H4) == true
@test alphaval(MVLTLFPTableau, ⊥, →(p, α), H4) == true
@test alphaval(MVLTLFPTableau, ⊥, →(p, β), H4) == true
@test alphaval(MVLTLFPTableau, ⊥, →(p, ⊤), H4) == true
@test alphaval(MVLTLFPTableau, α, →(p, ⊥), H4) == false
@test alphaval(MVLTLFPTableau, α, →(p, α), H4) == true
@test alphaval(MVLTLFPTableau, α, →(p, β), H4) == false
@test alphaval(MVLTLFPTableau, α, →(p, ⊤), H4) == true
@test alphaval(MVLTLFPTableau, β, →(p, ⊥), H4) == false
@test alphaval(MVLTLFPTableau, β, →(p, α), H4) == false
@test alphaval(MVLTLFPTableau, β, →(p, β), H4) == true
@test alphaval(MVLTLFPTableau, β, →(p, ⊤), H4) == true
@test alphaval(MVLTLFPTableau, ⊤, →(p, ⊥), H4) == false
@test alphaval(MVLTLFPTableau, ⊤, →(p, α), H4) == false
@test alphaval(MVLTLFPTableau, ⊤, →(p, β), H4) == false
@test alphaval(MVLTLFPTableau, ⊤, →(p, ⊤), H4) == true

@test alphaval(MVLTLFPTableau, ⊥, →(⊥, p), H4) == true
@test alphaval(MVLTLFPTableau, ⊥, →(α, p), H4) == true
@test alphaval(MVLTLFPTableau, ⊥, →(β, p), H4) == true
@test alphaval(MVLTLFPTableau, ⊥, →(⊤, p), H4) == true
@test alphaval(MVLTLFPTableau, α, →(⊥, p), H4) == true
@test alphaval(MVLTLFPTableau, α, →(α, p), H4) == false
@test alphaval(MVLTLFPTableau, α, →(β, p), H4) == true
@test alphaval(MVLTLFPTableau, α, →(⊤, p), H4) == false
@test alphaval(MVLTLFPTableau, β, →(⊥, p), H4) == true
@test alphaval(MVLTLFPTableau, β, →(α, p), H4) == true
@test alphaval(MVLTLFPTableau, β, →(β, p), H4) == false
@test alphaval(MVLTLFPTableau, β, →(⊤, p), H4) == false
@test alphaval(MVLTLFPTableau, ⊤, →(⊥, p), H4) == true
@test alphaval(MVLTLFPTableau, ⊤, →(α, p), H4) == false
@test alphaval(MVLTLFPTableau, ⊤, →(β, p), H4) == false
@test alphaval(MVLTLFPTableau, ⊤, →(⊤, p), H4) == false

@test alphaval(
    MVLTLFPTableau,
    ⊥,
    →(p, p),
    H4
) == true
@test alphaval(
    MVLTLFPTableau,
    α,
    →(p, p),
    H4
) == true
@test alphaval(
    MVLTLFPTableau,
    β,
    →(p, p),
    H4
) == true
@test alphaval(
    MVLTLFPTableau,
    ⊤,
    →(p, p),
    H4
) == true

@test alphaval(
    MVLTLFPTableau,
    ⊥,
    →(p, q),
    H4
) == true
@test alphaval(
    MVLTLFPTableau,
    α,
    →(p, q),
    H4
) == false
@test alphaval(
    MVLTLFPTableau,
    β,
    →(p, q),
    H4
) == false
@test alphaval(
    MVLTLFPTableau,
    ⊤,
    →(p, q),
    H4
) == false

@test alphaval(
    MVLTLFPTableau,
    ⊥,
    →(q, p),
    H4
) == true
@test alphaval(
    MVLTLFPTableau,
    α,
    →(q, p),
    H4
) == false
@test alphaval(
    MVLTLFPTableau,
    β,
    →(q, p),
    H4
) == false
@test alphaval(
    MVLTLFPTableau,
    ⊤,
    →(q, p),
    H4
) == false
