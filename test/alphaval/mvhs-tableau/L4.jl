################################################################################
#### Ł4 ########################################################################
################################################################################

using SoleLogics.ManyValuedLogics: Ł4, getdomain
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

timeout = 30

################################################################################
## Base cases ##################################################################
################################################################################

for i ∈ getdomain(Ł4)
    for j ∈ getdomain(Ł4)
        @test alphaval(
            MVHSTableau,
            i,
            j,
        Ł4) == alphasat(MVHSTableau, i, j, Ł4)
        for k ∈ getdomain(Ł4)
            @test alphaval(
                MVHSTableau,
                i,
                ∨(j,k),
                Ł4
            ) == alphasat(MVHSTableau, i, ∨(j,k), Ł4)
            @test alphaval(
                MVHSTableau,
                i,
                ∧(j,k),
                Ł4
            ) == alphasat(MVHSTableau, i, ∧(j,k), Ł4)
            @test alphaval(
                MVHSTableau,
                i,
                →(j,k),
                Ł4
            ) == alphasat(MVHSTableau, i, →(j,k), Ł4)
        end
    end
end

@test alphaval(MVHSTableau, ⊥, p, Ł4) == true
@test alphaval(MVHSTableau, α, p, Ł4) == false
@test alphaval(MVHSTableau, β, p, Ł4) == false
@test alphaval(MVHSTableau, ⊤, p, Ł4) == false

################################################################################
## (Strong) disjunction ########################################################
################################################################################

@test alphaval(MVHSTableau, ⊥, ∨(p, ⊥), Ł4) == true
@test alphaval(MVHSTableau, ⊥, ∨(p, α), Ł4) == true
@test alphaval(MVHSTableau, ⊥, ∨(p, β), Ł4) == true
@test alphaval(MVHSTableau, ⊥, ∨(p, ⊤), Ł4) == true
@test alphaval(MVHSTableau, α, ∨(p, ⊥), Ł4) == false
@test alphaval(MVHSTableau, α, ∨(p, α), Ł4) == true
@test alphaval(MVHSTableau, α, ∨(p, β), Ł4) == true
@test alphaval(MVHSTableau, α, ∨(p, ⊤), Ł4) == true
@test alphaval(MVHSTableau, β, ∨(p, ⊥), Ł4) == false
@test alphaval(MVHSTableau, β, ∨(p, α), Ł4) == false
@test alphaval(MVHSTableau, β, ∨(p, β), Ł4) == true
@test alphaval(MVHSTableau, β, ∨(p, ⊤), Ł4) == true
@test alphaval(MVHSTableau, ⊤, ∨(p, ⊥), Ł4) == false
@test alphaval(MVHSTableau, ⊤, ∨(p, α), Ł4) == false
@test alphaval(MVHSTableau, ⊤, ∨(p, β), Ł4) == false
@test alphaval(MVHSTableau, ⊤, ∨(p, ⊤), Ł4) == true

@test alphaval(MVHSTableau, ⊥, ∨(⊥, p), Ł4) == true
@test alphaval(MVHSTableau, ⊥, ∨(α, p), Ł4) == true 
@test alphaval(MVHSTableau, ⊥, ∨(β, p), Ł4) == true 
@test alphaval(MVHSTableau, ⊥, ∨(⊤, p), Ł4) == true 
@test alphaval(MVHSTableau, α, ∨(⊥, p), Ł4) == false
@test alphaval(MVHSTableau, α, ∨(α, p), Ł4) == true 
@test alphaval(MVHSTableau, α, ∨(β, p), Ł4) == true 
@test alphaval(MVHSTableau, α, ∨(⊤, p), Ł4) == true 
@test alphaval(MVHSTableau, β, ∨(⊥, p), Ł4) == false 
@test alphaval(MVHSTableau, β, ∨(α, p), Ł4) == false 
@test alphaval(MVHSTableau, β, ∨(β, p), Ł4) == true 
@test alphaval(MVHSTableau, β, ∨(⊤, p), Ł4) == true 
@test alphaval(MVHSTableau, ⊤, ∨(⊥, p), Ł4) == false 
@test alphaval(MVHSTableau, ⊤, ∨(α, p), Ł4) == false 
@test alphaval(MVHSTableau, ⊤, ∨(β, p), Ł4) == false 
@test alphaval(MVHSTableau, ⊤, ∨(⊤, p), Ł4) == true 

@test alphaval(
    MVHSTableau,
    ⊥,
    ∨(p, p),
    Ł4
) == true
@test alphaval(
    MVHSTableau,
    α,
    ∨(p, p),
    Ł4
) == false
@test alphaval(
    MVHSTableau,
    β,
    ∨(p, p),
    Ł4
) == false
@test alphaval(
    MVHSTableau,
    ⊤,
    ∨(p, p),
    Ł4
) == false

@test alphaval(
    MVHSTableau,
    ⊥,
    ∨(p, q),
    Ł4
) == true
@test alphaval(
    MVHSTableau,
    α,
    ∨(p, q),
    Ł4
) == false
@test alphaval(
    MVHSTableau,
    β,
    ∨(p, q),
    Ł4
) == false
@test alphaval(
    MVHSTableau,
    ⊤,
    ∨(p, q),
    Ł4
) == false

@test alphaval(
    MVHSTableau,
    ⊥,
    ∨(q, p),
    Ł4
) == true
@test alphaval(
    MVHSTableau,
    α,
    ∨(q, p),
    Ł4
) == false
@test alphaval(
    MVHSTableau,
    β,
    ∨(q, p),
    Ł4
) == false
@test alphaval(
    MVHSTableau,
    ⊤,
    ∨(q, p),
    Ł4
) == false

################################################################################
## (Strong) conjunction ########################################################
################################################################################

@test alphaval(MVHSTableau, ⊥, ∧(p, ⊥), Ł4) == true
@test alphaval(MVHSTableau, ⊥, ∧(p, α), Ł4) == true
@test alphaval(MVHSTableau, ⊥, ∧(p, β), Ł4) == true
@test alphaval(MVHSTableau, ⊥, ∧(p, ⊤), Ł4) == true
@test alphaval(MVHSTableau, α, ∧(p, ⊥), Ł4) == false
@test alphaval(MVHSTableau, α, ∧(p, α), Ł4) == false
@test alphaval(MVHSTableau, α, ∧(p, β), Ł4) == false
@test alphaval(MVHSTableau, α, ∧(p, ⊤), Ł4) == false
@test alphaval(MVHSTableau, β, ∧(p, ⊥), Ł4) == false
@test alphaval(MVHSTableau, β, ∧(p, α), Ł4) == false
@test alphaval(MVHSTableau, β, ∧(p, β), Ł4) == false
@test alphaval(MVHSTableau, β, ∧(p, ⊤), Ł4) == false
@test alphaval(MVHSTableau, ⊤, ∧(p, ⊥), Ł4) == false
@test alphaval(MVHSTableau, ⊤, ∧(p, α), Ł4) == false
@test alphaval(MVHSTableau, ⊤, ∧(p, β), Ł4) == false
@test alphaval(MVHSTableau, ⊤, ∧(p, ⊤), Ł4) == false

@test alphaval(MVHSTableau, ⊥, ∧(⊥, p), Ł4) == true 
@test alphaval(MVHSTableau, ⊥, ∧(α, p), Ł4) == true 
@test alphaval(MVHSTableau, ⊥, ∧(β, p), Ł4) == true 
@test alphaval(MVHSTableau, ⊥, ∧(⊤, p), Ł4) == true 
@test alphaval(MVHSTableau, α, ∧(⊥, p), Ł4) == false
@test alphaval(MVHSTableau, α, ∧(α, p), Ł4) == false 
@test alphaval(MVHSTableau, α, ∧(β, p), Ł4) == false 
@test alphaval(MVHSTableau, α, ∧(⊤, p), Ł4) == false 
@test alphaval(MVHSTableau, β, ∧(⊥, p), Ł4) == false 
@test alphaval(MVHSTableau, β, ∧(α, p), Ł4) == false 
@test alphaval(MVHSTableau, β, ∧(β, p), Ł4) == false 
@test alphaval(MVHSTableau, β, ∧(⊤, p), Ł4) == false 
@test alphaval(MVHSTableau, ⊤, ∧(⊥, p), Ł4) == false 
@test alphaval(MVHSTableau, ⊤, ∧(α, p), Ł4) == false 
@test alphaval(MVHSTableau, ⊤, ∧(β, p), Ł4) == false 
@test alphaval(MVHSTableau, ⊤, ∧(⊤, p), Ł4) == false 

@test alphaval(
    MVHSTableau,
    ⊥,
    ∧(p, p),
    Ł4
) == true
@test alphaval(
    MVHSTableau,
    α,
    ∧(p, p),
    Ł4
) == false
@test alphaval(
    MVHSTableau,
    β,
    ∧(p, p),
    Ł4
) == false
@test alphaval(
    MVHSTableau,
    ⊤,
    ∧(p, p),
    Ł4
) == false

@test alphaval(
    MVHSTableau,
    ⊥,
    ∧(p, q),
    Ł4
) == true
@test alphaval(
    MVHSTableau,
    α,
    ∧(p, q),
    Ł4
) == false
@test alphaval(
    MVHSTableau,
    β,
    ∧(p, q),
    Ł4
) == false
@test alphaval(
    MVHSTableau,
    ⊤,
    ∧(p, q),
    Ł4
) == false

@test alphaval(
    MVHSTableau,
    ⊥,
    ∧(q, p),
    Ł4
) == true
@test alphaval(
    MVHSTableau,
    α,
    ∧(q, p),
    Ł4
) == false
@test alphaval(
    MVHSTableau,
    β,
    ∧(q, p),
    Ł4
) == false
@test alphaval(
    MVHSTableau,
    ⊤,
    ∧(q, p),
    Ł4
) == false

################################################################################
## Implication #################################################################
################################################################################

@test alphaval(MVHSTableau, ⊥, →(p, ⊥), Ł4) == true
@test alphaval(MVHSTableau, ⊥, →(p, α), Ł4) == true
@test alphaval(MVHSTableau, ⊥, →(p, β), Ł4) == true
@test alphaval(MVHSTableau, ⊥, →(p, ⊤), Ł4) == true
@test alphaval(MVHSTableau, α, →(p, ⊥), Ł4) == false
@test alphaval(MVHSTableau, α, →(p, α), Ł4) == true
@test alphaval(MVHSTableau, α, →(p, β), Ł4) == true
@test alphaval(MVHSTableau, α, →(p, ⊤), Ł4) == true
@test alphaval(MVHSTableau, β, →(p, ⊥), Ł4) == false
@test alphaval(MVHSTableau, β, →(p, α), Ł4) == false
@test alphaval(MVHSTableau, β, →(p, β), Ł4) == true
@test alphaval(MVHSTableau, β, →(p, ⊤), Ł4) == true
@test alphaval(MVHSTableau, ⊤, →(p, ⊥), Ł4) == false
@test alphaval(MVHSTableau, ⊤, →(p, α), Ł4) == false
@test alphaval(MVHSTableau, ⊤, →(p, β), Ł4) == false
@test alphaval(MVHSTableau, ⊤, →(p, ⊤), Ł4) == true

@test alphaval(MVHSTableau, ⊥, →(⊥, p), Ł4) == true
@test alphaval(MVHSTableau, ⊥, →(α, p), Ł4) == true
@test alphaval(MVHSTableau, ⊥, →(β, p), Ł4) == true
@test alphaval(MVHSTableau, ⊥, →(⊤, p), Ł4) == true
@test alphaval(MVHSTableau, α, →(⊥, p), Ł4) == true
@test alphaval(MVHSTableau, α, →(α, p), Ł4) == true
@test alphaval(MVHSTableau, α, →(β, p), Ł4) == true
@test alphaval(MVHSTableau, α, →(⊤, p), Ł4) == false
@test alphaval(MVHSTableau, β, →(⊥, p), Ł4) == true
@test alphaval(MVHSTableau, β, →(α, p), Ł4) == true
@test alphaval(MVHSTableau, β, →(β, p), Ł4) == false
@test alphaval(MVHSTableau, β, →(⊤, p), Ł4) == false
@test alphaval(MVHSTableau, ⊤, →(⊥, p), Ł4) == true
@test alphaval(MVHSTableau, ⊤, →(α, p), Ł4) == false
@test alphaval(MVHSTableau, ⊤, →(β, p), Ł4) == false
@test alphaval(MVHSTableau, ⊤, →(⊤, p), Ł4) == false

@test alphaval(
    MVHSTableau,
    ⊥,
    →(p, p),
    Ł4
) == true
@test alphaval(
    MVHSTableau,
    α,
    →(p, p),
    Ł4
) == true
@test alphaval(
    MVHSTableau,
    β,
    →(p, p),
    Ł4
) == true
@test alphaval(
    MVHSTableau,
    ⊤,
    →(p, p),
    Ł4
) == true

@test alphaval(
    MVHSTableau,
    ⊥,
    →(p, q),
    Ł4
) == true
@test alphaval(
    MVHSTableau,
    α,
    →(p, q),
    Ł4
) == false
@test alphaval(
    MVHSTableau,
    β,
    →(p, q),
    Ł4
) == false
@test alphaval(
    MVHSTableau,
    ⊤,
    →(p, q),
    Ł4
) == false

@test alphaval(
    MVHSTableau,
    ⊥,
    →(q, p),
    Ł4
) == true
@test alphaval(
    MVHSTableau,
    α,
    →(q, p),
    Ł4
) == false
@test alphaval(
    MVHSTableau,
    β,
    →(q, p),
    Ł4
) == false
@test alphaval(
    MVHSTableau,
    ⊤,
    →(q, p),
    Ł4
) == false
