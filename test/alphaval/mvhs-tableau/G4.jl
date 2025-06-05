################################################################################
#### G4 ########################################################################
################################################################################

using SoleLogics.ManyValuedLogics: G4, getdomain
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

for i ∈ getdomain(G4)
    for j ∈ getdomain(G4)
        @test alphaval(
            MVHSTableau,
            i,
            j,
        G4) == alphasat(MVHSTableau, i, j, G4)
        for k ∈ getdomain(G4)
            @test alphaval(
                MVHSTableau,
                i,
                ∨(j,k),
                G4
            ) == alphasat(MVHSTableau, i, ∨(j,k), G4)
            @test alphaval(
                MVHSTableau,
                i,
                ∧(j,k),
                G4
            ) == alphasat(MVHSTableau, i, ∧(j,k), G4)
            @test alphaval(
                MVHSTableau,
                i,
                →(j,k),
                G4
            ) == alphasat(MVHSTableau, i, →(j,k), G4)
        end
    end
end

@test alphaval(MVHSTableau, ⊥, p, G4) == true
@test alphaval(MVHSTableau, α, p, G4) == false
@test alphaval(MVHSTableau, β, p, G4) == false
@test alphaval(MVHSTableau, ⊤, p, G4) == false

################################################################################
## (Strong) disjunction ########################################################
################################################################################

@test alphaval(MVHSTableau, ⊥, ∨(p, ⊥), G4) == true
@test alphaval(MVHSTableau, ⊥, ∨(p, α), G4) == true
@test alphaval(MVHSTableau, ⊥, ∨(p, β), G4) == true
@test alphaval(MVHSTableau, ⊥, ∨(p, ⊤), G4) == true
@test alphaval(MVHSTableau, α, ∨(p, ⊥), G4) == false
@test alphaval(MVHSTableau, α, ∨(p, α), G4) == true
@test alphaval(MVHSTableau, α, ∨(p, β), G4) == true
@test alphaval(MVHSTableau, α, ∨(p, ⊤), G4) == true
@test alphaval(MVHSTableau, β, ∨(p, ⊥), G4) == false
@test alphaval(MVHSTableau, β, ∨(p, α), G4) == false
@test alphaval(MVHSTableau, β, ∨(p, β), G4) == true
@test alphaval(MVHSTableau, β, ∨(p, ⊤), G4) == true
@test alphaval(MVHSTableau, ⊤, ∨(p, ⊥), G4) == false
@test alphaval(MVHSTableau, ⊤, ∨(p, α), G4) == false
@test alphaval(MVHSTableau, ⊤, ∨(p, β), G4) == false
@test alphaval(MVHSTableau, ⊤, ∨(p, ⊤), G4) == true

@test alphaval(MVHSTableau, ⊥, ∨(⊥, p), G4) == true
@test alphaval(MVHSTableau, ⊥, ∨(α, p), G4) == true 
@test alphaval(MVHSTableau, ⊥, ∨(β, p), G4) == true 
@test alphaval(MVHSTableau, ⊥, ∨(⊤, p), G4) == true 
@test alphaval(MVHSTableau, α, ∨(⊥, p), G4) == false
@test alphaval(MVHSTableau, α, ∨(α, p), G4) == true 
@test alphaval(MVHSTableau, α, ∨(β, p), G4) == true 
@test alphaval(MVHSTableau, α, ∨(⊤, p), G4) == true 
@test alphaval(MVHSTableau, β, ∨(⊥, p), G4) == false 
@test alphaval(MVHSTableau, β, ∨(α, p), G4) == false 
@test alphaval(MVHSTableau, β, ∨(β, p), G4) == true 
@test alphaval(MVHSTableau, β, ∨(⊤, p), G4) == true 
@test alphaval(MVHSTableau, ⊤, ∨(⊥, p), G4) == false 
@test alphaval(MVHSTableau, ⊤, ∨(α, p), G4) == false 
@test alphaval(MVHSTableau, ⊤, ∨(β, p), G4) == false 
@test alphaval(MVHSTableau, ⊤, ∨(⊤, p), G4) == true 

@test alphaval(
    MVHSTableau,
    ⊥,
    ∨(p, p),
    G4
) == true
@test alphaval(
    MVHSTableau,
    α,
    ∨(p, p),
    G4
) == false
@test alphaval(
    MVHSTableau,
    β,
    ∨(p, p),
    G4
) == false
@test alphaval(
    MVHSTableau,
    ⊤,
    ∨(p, p),
    G4
) == false

@test alphaval(
    MVHSTableau,
    ⊥,
    ∨(p, q),
    G4
) == true
@test alphaval(
    MVHSTableau,
    α,
    ∨(p, q),
    G4
) == false
@test alphaval(
    MVHSTableau,
    β,
    ∨(p, q),
    G4
) == false
@test alphaval(
    MVHSTableau,
    ⊤,
    ∨(p, q),
    G4
) == false

@test alphaval(
    MVHSTableau,
    ⊥,
    ∨(q, p),
    G4
) == true
@test alphaval(
    MVHSTableau,
    α,
    ∨(q, p),
    G4
) == false
@test alphaval(
    MVHSTableau,
    β,
    ∨(q, p),
    G4
) == false
@test alphaval(
    MVHSTableau,
    ⊤,
    ∨(q, p),
    G4
) == false

################################################################################
## (Strong) conjunction ########################################################
################################################################################

@test alphaval(MVHSTableau, ⊥, ∧(p, ⊥), G4) == true
@test alphaval(MVHSTableau, ⊥, ∧(p, α), G4) == true
@test alphaval(MVHSTableau, ⊥, ∧(p, β), G4) == true
@test alphaval(MVHSTableau, ⊥, ∧(p, ⊤), G4) == true
@test alphaval(MVHSTableau, α, ∧(p, ⊥), G4) == false
@test alphaval(MVHSTableau, α, ∧(p, α), G4) == false
@test alphaval(MVHSTableau, α, ∧(p, β), G4) == false
@test alphaval(MVHSTableau, α, ∧(p, ⊤), G4) == false
@test alphaval(MVHSTableau, β, ∧(p, ⊥), G4) == false
@test alphaval(MVHSTableau, β, ∧(p, α), G4) == false
@test alphaval(MVHSTableau, β, ∧(p, β), G4) == false
@test alphaval(MVHSTableau, β, ∧(p, ⊤), G4) == false
@test alphaval(MVHSTableau, ⊤, ∧(p, ⊥), G4) == false
@test alphaval(MVHSTableau, ⊤, ∧(p, α), G4) == false
@test alphaval(MVHSTableau, ⊤, ∧(p, β), G4) == false
@test alphaval(MVHSTableau, ⊤, ∧(p, ⊤), G4) == false

@test alphaval(MVHSTableau, ⊥, ∧(⊥, p), G4) == true 
@test alphaval(MVHSTableau, ⊥, ∧(α, p), G4) == true 
@test alphaval(MVHSTableau, ⊥, ∧(β, p), G4) == true 
@test alphaval(MVHSTableau, ⊥, ∧(⊤, p), G4) == true 
@test alphaval(MVHSTableau, α, ∧(⊥, p), G4) == false
@test alphaval(MVHSTableau, α, ∧(α, p), G4) == false 
@test alphaval(MVHSTableau, α, ∧(β, p), G4) == false 
@test alphaval(MVHSTableau, α, ∧(⊤, p), G4) == false 
@test alphaval(MVHSTableau, β, ∧(⊥, p), G4) == false 
@test alphaval(MVHSTableau, β, ∧(α, p), G4) == false 
@test alphaval(MVHSTableau, β, ∧(β, p), G4) == false 
@test alphaval(MVHSTableau, β, ∧(⊤, p), G4) == false 
@test alphaval(MVHSTableau, ⊤, ∧(⊥, p), G4) == false 
@test alphaval(MVHSTableau, ⊤, ∧(α, p), G4) == false 
@test alphaval(MVHSTableau, ⊤, ∧(β, p), G4) == false 
@test alphaval(MVHSTableau, ⊤, ∧(⊤, p), G4) == false 

@test alphaval(
    MVHSTableau,
    ⊥,
    ∧(p, p),
    G4
) == true
@test alphaval(
    MVHSTableau,
    α,
    ∧(p, p),
    G4
) == false
@test alphaval(
    MVHSTableau,
    β,
    ∧(p, p),
    G4
) == false
@test alphaval(
    MVHSTableau,
    ⊤,
    ∧(p, p),
    G4
) == false

@test alphaval(
    MVHSTableau,
    ⊥,
    ∧(p, q),
    G4
) == true
@test alphaval(
    MVHSTableau,
    α,
    ∧(p, q),
    G4
) == false
@test alphaval(
    MVHSTableau,
    β,
    ∧(p, q),
    G4
) == false
@test alphaval(
    MVHSTableau,
    ⊤,
    ∧(p, q),
    G4
) == false

@test alphaval(
    MVHSTableau,
    ⊥,
    ∧(q, p),
    G4
) == true
@test alphaval(
    MVHSTableau,
    α,
    ∧(q, p),
    G4
) == false
@test alphaval(
    MVHSTableau,
    β,
    ∧(q, p),
    G4
) == false
@test alphaval(
    MVHSTableau,
    ⊤,
    ∧(q, p),
    G4
) == false

################################################################################
## Implication #################################################################
################################################################################

@test alphaval(MVHSTableau, ⊥, →(p, ⊥), G4) == true
@test alphaval(MVHSTableau, ⊥, →(p, α), G4) == true
@test alphaval(MVHSTableau, ⊥, →(p, β), G4) == true
@test alphaval(MVHSTableau, ⊥, →(p, ⊤), G4) == true
@test alphaval(MVHSTableau, α, →(p, ⊥), G4) == false
@test alphaval(MVHSTableau, α, →(p, α), G4) == true
@test alphaval(MVHSTableau, α, →(p, β), G4) == true
@test alphaval(MVHSTableau, α, →(p, ⊤), G4) == true
@test alphaval(MVHSTableau, β, →(p, ⊥), G4) == false
@test alphaval(MVHSTableau, β, →(p, α), G4) == false
@test alphaval(MVHSTableau, β, →(p, β), G4) == true
@test alphaval(MVHSTableau, β, →(p, ⊤), G4) == true
@test alphaval(MVHSTableau, ⊤, →(p, ⊥), G4) == false
@test alphaval(MVHSTableau, ⊤, →(p, α), G4) == false
@test alphaval(MVHSTableau, ⊤, →(p, β), G4) == false
@test alphaval(MVHSTableau, ⊤, →(p, ⊤), G4) == true

@test alphaval(MVHSTableau, ⊥, →(⊥, p), G4) == true
@test alphaval(MVHSTableau, ⊥, →(α, p), G4) == true
@test alphaval(MVHSTableau, ⊥, →(β, p), G4) == true
@test alphaval(MVHSTableau, ⊥, →(⊤, p), G4) == true
@test alphaval(MVHSTableau, α, →(⊥, p), G4) == true
@test alphaval(MVHSTableau, α, →(α, p), G4) == false
@test alphaval(MVHSTableau, α, →(β, p), G4) == false
@test alphaval(MVHSTableau, α, →(⊤, p), G4) == false
@test alphaval(MVHSTableau, β, →(⊥, p), G4) == true
@test alphaval(MVHSTableau, β, →(α, p), G4) == false
@test alphaval(MVHSTableau, β, →(β, p), G4) == false
@test alphaval(MVHSTableau, β, →(⊤, p), G4) == false
@test alphaval(MVHSTableau, ⊤, →(⊥, p), G4) == true
@test alphaval(MVHSTableau, ⊤, →(α, p), G4) == false
@test alphaval(MVHSTableau, ⊤, →(β, p), G4) == false
@test alphaval(MVHSTableau, ⊤, →(⊤, p), G4) == false

@test alphaval(
    MVHSTableau,
    ⊥,
    →(p, p),
    G4
) == true
@test alphaval(
    MVHSTableau,
    α,
    →(p, p),
    G4
) == true
@test alphaval(
    MVHSTableau,
    β,
    →(p, p),
    G4
) == true
@test alphaval(
    MVHSTableau,
    ⊤,
    →(p, p),
    G4
) == true

@test alphaval(
    MVHSTableau,
    ⊥,
    →(p, q),
    G4
) == true
@test alphaval(
    MVHSTableau,
    α,
    →(p, q),
    G4
) == false
@test alphaval(
    MVHSTableau,
    β,
    →(p, q),
    G4
) == false
@test alphaval(
    MVHSTableau,
    ⊤,
    →(p, q),
    G4
) == false

@test alphaval(
    MVHSTableau,
    ⊥,
    →(q, p),
    G4
) == true
@test alphaval(
    MVHSTableau,
    α,
    →(q, p),
    G4
) == false
@test alphaval(
    MVHSTableau,
    β,
    →(q, p),
    G4
) == false
@test alphaval(
    MVHSTableau,
    ⊤,
    →(q, p),
    G4
) == false
