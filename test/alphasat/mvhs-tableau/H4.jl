################################################################################
#### H4 ########################################################################
################################################################################

using SoleLogics.ManyValuedLogics: H4
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

@test alphasat(MVHSTableau, ⊥, ⊥, H4) == true
@test alphasat(MVHSTableau, ⊥, α, H4) == true
@test alphasat(MVHSTableau, ⊥, β, H4) == true
@test alphasat(MVHSTableau, ⊥, ⊤, H4) == true
@test alphasat(MVHSTableau, α, ⊥, H4) == false
@test alphasat(MVHSTableau, α, α, H4) == true
@test alphasat(MVHSTableau, α, β, H4) == false
@test alphasat(MVHSTableau, α, ⊤, H4) == true
@test alphasat(MVHSTableau, β, ⊥, H4) == false
@test alphasat(MVHSTableau, β, α, H4) == false
@test alphasat(MVHSTableau, β, β, H4) == true
@test alphasat(MVHSTableau, β, ⊤, H4) == true
@test alphasat(MVHSTableau, ⊤, ⊥, H4) == false
@test alphasat(MVHSTableau, ⊤, α, H4) == false
@test alphasat(MVHSTableau, ⊤, β, H4) == false
@test alphasat(MVHSTableau, ⊤, ⊤, H4) == true

@test alphasat(MVHSTableau, ⊥, p, H4) == true
@test alphasat(MVHSTableau, α, p, H4) == true
@test alphasat(MVHSTableau, β, p, H4) == true
@test alphasat(MVHSTableau, ⊤, p, H4) == true

################################################################################
## (Strong) disjuction #########################################################
################################################################################

@test alphasat(MVHSTableau, ⊥, ∨(⊥, ⊥), H4) == true
@test alphasat(MVHSTableau, ⊥, ∨(⊥, α), H4) == true
@test alphasat(MVHSTableau, ⊥, ∨(⊥, β), H4) == true
@test alphasat(MVHSTableau, ⊥, ∨(⊥, ⊤), H4) == true
@test alphasat(MVHSTableau, ⊥, ∨(α, ⊥), H4) == true
@test alphasat(MVHSTableau, ⊥, ∨(α, α), H4) == true
@test alphasat(MVHSTableau, ⊥, ∨(α, β), H4) == true
@test alphasat(MVHSTableau, ⊥, ∨(α, ⊤), H4) == true
@test alphasat(MVHSTableau, ⊥, ∨(β, ⊥), H4) == true
@test alphasat(MVHSTableau, ⊥, ∨(β, α), H4) == true
@test alphasat(MVHSTableau, ⊥, ∨(β, β), H4) == true
@test alphasat(MVHSTableau, ⊥, ∨(β, ⊤), H4) == true
@test alphasat(MVHSTableau, ⊥, ∨(⊤, ⊥), H4) == true
@test alphasat(MVHSTableau, ⊥, ∨(⊤, α), H4) == true
@test alphasat(MVHSTableau, ⊥, ∨(⊤, β), H4) == true
@test alphasat(MVHSTableau, ⊥, ∨(⊤, ⊤), H4) == true

@test alphasat(MVHSTableau, α, ∨(⊥, ⊥), H4) == false
@test alphasat(MVHSTableau, α, ∨(⊥, α), H4) == true
@test alphasat(MVHSTableau, α, ∨(⊥, β), H4) == false
@test alphasat(MVHSTableau, α, ∨(⊥, ⊤), H4) == true
@test alphasat(MVHSTableau, α, ∨(α, ⊥), H4) == true
@test alphasat(MVHSTableau, α, ∨(α, α), H4) == true
@test alphasat(MVHSTableau, α, ∨(α, β), H4) == true
@test alphasat(MVHSTableau, α, ∨(α, ⊤), H4) == true
@test alphasat(MVHSTableau, α, ∨(β, ⊥), H4) == false
@test alphasat(MVHSTableau, α, ∨(β, α), H4) == true
@test alphasat(MVHSTableau, α, ∨(β, β), H4) == false
@test alphasat(MVHSTableau, α, ∨(β, ⊤), H4) == true
@test alphasat(MVHSTableau, α, ∨(⊤, ⊥), H4) == true
@test alphasat(MVHSTableau, α, ∨(⊤, α), H4) == true
@test alphasat(MVHSTableau, α, ∨(⊤, β), H4) == true
@test alphasat(MVHSTableau, α, ∨(⊤, ⊤), H4) == true

@test alphasat(MVHSTableau, β, ∨(⊥, ⊥), H4) == false
@test alphasat(MVHSTableau, β, ∨(⊥, α), H4) == false
@test alphasat(MVHSTableau, β, ∨(⊥, β), H4) == true
@test alphasat(MVHSTableau, β, ∨(⊥, ⊤), H4) == true
@test alphasat(MVHSTableau, β, ∨(α, ⊥), H4) == false
@test alphasat(MVHSTableau, β, ∨(α, α), H4) == false
@test alphasat(MVHSTableau, β, ∨(α, β), H4) == true
@test alphasat(MVHSTableau, β, ∨(α, ⊤), H4) == true
@test alphasat(MVHSTableau, β, ∨(β, ⊥), H4) == true
@test alphasat(MVHSTableau, β, ∨(β, α), H4) == true
@test alphasat(MVHSTableau, β, ∨(β, β), H4) == true
@test alphasat(MVHSTableau, β, ∨(β, ⊤), H4) == true
@test alphasat(MVHSTableau, β, ∨(⊤, ⊥), H4) == true
@test alphasat(MVHSTableau, β, ∨(⊤, α), H4) == true
@test alphasat(MVHSTableau, β, ∨(⊤, β), H4) == true
@test alphasat(MVHSTableau, β, ∨(⊤, ⊤), H4) == true

@test alphasat(MVHSTableau, ⊤, ∨(⊥, ⊥), H4) == false
@test alphasat(MVHSTableau, ⊤, ∨(⊥, α), H4) == false
@test alphasat(MVHSTableau, ⊤, ∨(⊥, β), H4) == false
@test alphasat(MVHSTableau, ⊤, ∨(⊥, ⊤), H4) == true
@test alphasat(MVHSTableau, ⊤, ∨(α, ⊥), H4) == false
@test alphasat(MVHSTableau, ⊤, ∨(α, α), H4) == false
@test alphasat(MVHSTableau, ⊤, ∨(α, β), H4) == true
@test alphasat(MVHSTableau, ⊤, ∨(α, ⊤), H4) == true
@test alphasat(MVHSTableau, ⊤, ∨(β, ⊥), H4) == false
@test alphasat(MVHSTableau, ⊤, ∨(β, α), H4) == true
@test alphasat(MVHSTableau, ⊤, ∨(β, β), H4) == false
@test alphasat(MVHSTableau, ⊤, ∨(β, ⊤), H4) == true
@test alphasat(MVHSTableau, ⊤, ∨(⊤, ⊥), H4) == true
@test alphasat(MVHSTableau, ⊤, ∨(⊤, α), H4) == true
@test alphasat(MVHSTableau, ⊤, ∨(⊤, β), H4) == true
@test alphasat(MVHSTableau, ⊤, ∨(⊤, ⊤), H4) == true

@test alphasat(MVHSTableau, ⊥, ∨(p, ⊥), H4) == true
@test alphasat(MVHSTableau, ⊥, ∨(p, α), H4) == true
@test alphasat(MVHSTableau, ⊥, ∨(p, β), H4) == true
@test alphasat(MVHSTableau, ⊥, ∨(p, ⊤), H4) == true
@test alphasat(MVHSTableau, α, ∨(p, ⊥), H4) == true
@test alphasat(MVHSTableau, α, ∨(p, α), H4) == true
@test alphasat(MVHSTableau, α, ∨(p, β), H4) == true
@test alphasat(MVHSTableau, α, ∨(p, ⊤), H4) == true
@test alphasat(MVHSTableau, β, ∨(p, ⊥), H4) == true
@test alphasat(MVHSTableau, β, ∨(p, α), H4) == true
@test alphasat(MVHSTableau, β, ∨(p, β), H4) == true
@test alphasat(MVHSTableau, β, ∨(p, ⊤), H4) == true
@test alphasat(MVHSTableau, ⊤, ∨(p, ⊥), H4) == true
@test alphasat(MVHSTableau, ⊤, ∨(p, α), H4) == true
@test alphasat(MVHSTableau, ⊤, ∨(p, β), H4) == true
@test alphasat(MVHSTableau, ⊤, ∨(p, ⊤), H4) == true

@test alphasat(MVHSTableau, ⊥, ∨(⊥, p), H4) == true
@test alphasat(MVHSTableau, ⊥, ∨(α, p), H4) == true
@test alphasat(MVHSTableau, ⊥, ∨(β, p), H4) == true
@test alphasat(MVHSTableau, ⊥, ∨(⊤, p), H4) == true
@test alphasat(MVHSTableau, α, ∨(⊥, p), H4) == true
@test alphasat(MVHSTableau, α, ∨(α, p), H4) == true
@test alphasat(MVHSTableau, α, ∨(β, p), H4) == true
@test alphasat(MVHSTableau, α, ∨(⊤, p), H4) == true
@test alphasat(MVHSTableau, β, ∨(⊥, p), H4) == true
@test alphasat(MVHSTableau, β, ∨(α, p), H4) == true
@test alphasat(MVHSTableau, β, ∨(β, p), H4) == true
@test alphasat(MVHSTableau, β, ∨(⊤, p), H4) == true
@test alphasat(MVHSTableau, ⊤, ∨(⊥, p), H4) == true
@test alphasat(MVHSTableau, ⊤, ∨(α, p), H4) == true
@test alphasat(MVHSTableau, ⊤, ∨(β, p), H4) == true
@test alphasat(MVHSTableau, ⊤, ∨(⊤, p), H4) == true

@test alphasat(MVHSTableau, ⊥, ∨(p, p), H4)
@test alphasat(MVHSTableau, α, ∨(p, p), H4)
@test alphasat(MVHSTableau, β, ∨(p, p), H4)
@test alphasat(MVHSTableau, ⊤, ∨(p, p), H4)

@test alphasat(MVHSTableau, ⊥, ∨(p, q), H4)
@test alphasat(MVHSTableau, α, ∨(p, q), H4)
@test alphasat(MVHSTableau, β, ∨(p, q), H4)
@test alphasat(MVHSTableau, ⊤, ∨(p, q), H4)

@test alphasat(MVHSTableau, ⊥, ∨(q, q), H4)
@test alphasat(MVHSTableau, α, ∨(q, q), H4)
@test alphasat(MVHSTableau, β, ∨(q, q), H4)
@test alphasat(MVHSTableau, ⊤, ∨(q, q), H4)

################################################################################
## (Strong) conjunction ########################################################
################################################################################

@test alphasat(MVHSTableau, ⊥, ∧(⊥, ⊥), H4) == true
@test alphasat(MVHSTableau, ⊥, ∧(⊥, α), H4) == true
@test alphasat(MVHSTableau, ⊥, ∧(⊥, β), H4) == true
@test alphasat(MVHSTableau, ⊥, ∧(⊥, ⊤), H4) == true
@test alphasat(MVHSTableau, ⊥, ∧(α, ⊥), H4) == true
@test alphasat(MVHSTableau, ⊥, ∧(α, α), H4) == true
@test alphasat(MVHSTableau, ⊥, ∧(α, β), H4) == true
@test alphasat(MVHSTableau, ⊥, ∧(α, ⊤), H4) == true
@test alphasat(MVHSTableau, ⊥, ∧(β, ⊥), H4) == true
@test alphasat(MVHSTableau, ⊥, ∧(β, α), H4) == true
@test alphasat(MVHSTableau, ⊥, ∧(β, β), H4) == true
@test alphasat(MVHSTableau, ⊥, ∧(β, ⊤), H4) == true
@test alphasat(MVHSTableau, ⊥, ∧(⊤, ⊥), H4) == true
@test alphasat(MVHSTableau, ⊥, ∧(⊤, α), H4) == true
@test alphasat(MVHSTableau, ⊥, ∧(⊤, β), H4) == true
@test alphasat(MVHSTableau, ⊥, ∧(⊤, ⊤), H4) == true

@test alphasat(MVHSTableau, α, ∧(⊥, ⊥), H4) == false
@test alphasat(MVHSTableau, α, ∧(⊥, α), H4) == false
@test alphasat(MVHSTableau, α, ∧(⊥, β), H4) == false
@test alphasat(MVHSTableau, α, ∧(⊥, ⊤), H4) == false
@test alphasat(MVHSTableau, α, ∧(α, ⊥), H4) == false
@test alphasat(MVHSTableau, α, ∧(α, α), H4) == true
@test alphasat(MVHSTableau, α, ∧(α, β), H4) == false
@test alphasat(MVHSTableau, α, ∧(α, ⊤), H4) == true
@test alphasat(MVHSTableau, α, ∧(β, ⊥), H4) == false
@test alphasat(MVHSTableau, α, ∧(β, α), H4) == false
@test alphasat(MVHSTableau, α, ∧(β, β), H4) == false
@test alphasat(MVHSTableau, α, ∧(β, ⊤), H4) == false
@test alphasat(MVHSTableau, α, ∧(⊤, ⊥), H4) == false
@test alphasat(MVHSTableau, α, ∧(⊤, α), H4) == true
@test alphasat(MVHSTableau, α, ∧(⊤, β), H4) == false
@test alphasat(MVHSTableau, α, ∧(⊤, ⊤), H4) == true

@test alphasat(MVHSTableau, β, ∧(⊥, ⊥), H4) == false
@test alphasat(MVHSTableau, β, ∧(⊥, α), H4) == false
@test alphasat(MVHSTableau, β, ∧(⊥, β), H4) == false
@test alphasat(MVHSTableau, β, ∧(⊥, ⊤), H4) == false
@test alphasat(MVHSTableau, β, ∧(α, ⊥), H4) == false
@test alphasat(MVHSTableau, β, ∧(α, α), H4) == false
@test alphasat(MVHSTableau, β, ∧(α, β), H4) == false
@test alphasat(MVHSTableau, β, ∧(α, ⊤), H4) == false
@test alphasat(MVHSTableau, β, ∧(β, ⊥), H4) == false
@test alphasat(MVHSTableau, β, ∧(β, α), H4) == false
@test alphasat(MVHSTableau, β, ∧(β, β), H4) == true
@test alphasat(MVHSTableau, β, ∧(β, ⊤), H4) == true
@test alphasat(MVHSTableau, β, ∧(⊤, ⊥), H4) == false
@test alphasat(MVHSTableau, β, ∧(⊤, α), H4) == false
@test alphasat(MVHSTableau, β, ∧(⊤, β), H4) == true
@test alphasat(MVHSTableau, β, ∧(⊤, ⊤), H4) == true

@test alphasat(MVHSTableau, ⊤, ∧(⊥, ⊥), H4) == false
@test alphasat(MVHSTableau, ⊤, ∧(⊥, α), H4) == false
@test alphasat(MVHSTableau, ⊤, ∧(⊥, β), H4) == false
@test alphasat(MVHSTableau, ⊤, ∧(⊥, ⊤), H4) == false
@test alphasat(MVHSTableau, ⊤, ∧(α, ⊥), H4) == false
@test alphasat(MVHSTableau, ⊤, ∧(α, α), H4) == false
@test alphasat(MVHSTableau, ⊤, ∧(α, β), H4) == false
@test alphasat(MVHSTableau, ⊤, ∧(α, ⊤), H4) == false
@test alphasat(MVHSTableau, ⊤, ∧(β, ⊥), H4) == false
@test alphasat(MVHSTableau, ⊤, ∧(β, α), H4) == false
@test alphasat(MVHSTableau, ⊤, ∧(β, β), H4) == false
@test alphasat(MVHSTableau, ⊤, ∧(β, ⊤), H4) == false
@test alphasat(MVHSTableau, ⊤, ∧(⊤, ⊥), H4) == false
@test alphasat(MVHSTableau, ⊤, ∧(⊤, α), H4) == false
@test alphasat(MVHSTableau, ⊤, ∧(⊤, β), H4) == false
@test alphasat(MVHSTableau, ⊤, ∧(⊤, ⊤), H4) == true

@test alphasat(MVHSTableau, ⊥, ∧(p, ⊥), H4) == true
@test alphasat(MVHSTableau, ⊥, ∧(p, α), H4) == true
@test alphasat(MVHSTableau, ⊥, ∧(p, β), H4) == true
@test alphasat(MVHSTableau, ⊥, ∧(p, ⊤), H4) == true
@test alphasat(MVHSTableau, α, ∧(p, ⊥), H4) == false
@test alphasat(MVHSTableau, α, ∧(p, α), H4) == true
@test alphasat(MVHSTableau, α, ∧(p, β), H4) == false
@test alphasat(MVHSTableau, α, ∧(p, ⊤), H4) == true
@test alphasat(MVHSTableau, β, ∧(p, ⊥), H4) == false
@test alphasat(MVHSTableau, β, ∧(p, α), H4) == false
@test alphasat(MVHSTableau, β, ∧(p, β), H4) == true
@test alphasat(MVHSTableau, β, ∧(p, ⊤), H4) == true
@test alphasat(MVHSTableau, ⊤, ∧(p, ⊥), H4) == false
@test alphasat(MVHSTableau, ⊤, ∧(p, α), H4) == false
@test alphasat(MVHSTableau, ⊤, ∧(p, β), H4) == false
@test alphasat(MVHSTableau, ⊤, ∧(p, ⊤), H4) == true

@test alphasat(MVHSTableau, ⊥, ∧(⊥, p), H4) == true
@test alphasat(MVHSTableau, ⊥, ∧(α, p), H4) == true
@test alphasat(MVHSTableau, ⊥, ∧(β, p), H4) == true
@test alphasat(MVHSTableau, ⊥, ∧(⊤, p), H4) == true
@test alphasat(MVHSTableau, α, ∧(⊥, p), H4) == false
@test alphasat(MVHSTableau, α, ∧(α, p), H4) == true
@test alphasat(MVHSTableau, α, ∧(β, p), H4) == false
@test alphasat(MVHSTableau, α, ∧(⊤, p), H4) == true
@test alphasat(MVHSTableau, β, ∧(⊥, p), H4) == false
@test alphasat(MVHSTableau, β, ∧(α, p), H4) == false
@test alphasat(MVHSTableau, β, ∧(β, p), H4) == true
@test alphasat(MVHSTableau, β, ∧(⊤, p), H4) == true
@test alphasat(MVHSTableau, ⊤, ∧(⊥, p), H4) == false
@test alphasat(MVHSTableau, ⊤, ∧(α, p), H4) == false
@test alphasat(MVHSTableau, ⊤, ∧(β, p), H4) == false
@test alphasat(MVHSTableau, ⊤, ∧(⊤, p), H4) == true

@test alphasat(MVHSTableau, ⊥, ∧(p, p), H4)
@test alphasat(MVHSTableau, α, ∧(p, p), H4)
@test alphasat(MVHSTableau, β, ∧(p, p), H4)
@test alphasat(MVHSTableau, ⊤, ∧(p, p), H4)

@test alphasat(MVHSTableau, ⊥, ∧(p, q), H4)
@test alphasat(MVHSTableau, α, ∧(p, q), H4)
@test alphasat(MVHSTableau, β, ∧(p, q), H4)
@test alphasat(MVHSTableau, ⊤, ∧(p, q), H4)

@test alphasat(MVHSTableau, ⊥, ∧(q, p), H4)
@test alphasat(MVHSTableau, α, ∧(q, p), H4)
@test alphasat(MVHSTableau, β, ∧(q, p), H4)
@test alphasat(MVHSTableau, ⊤, ∧(q, p), H4)

################################################################################
## Implication #################################################################
################################################################################

@test alphasat(MVHSTableau, ⊥, →(⊥, ⊥), H4) == true
@test alphasat(MVHSTableau, ⊥, →(⊥, α), H4) == true
@test alphasat(MVHSTableau, ⊥, →(⊥, β), H4) == true
@test alphasat(MVHSTableau, ⊥, →(⊥, ⊤), H4) == true
@test alphasat(MVHSTableau, ⊥, →(α, ⊥), H4) == true
@test alphasat(MVHSTableau, ⊥, →(α, α), H4) == true
@test alphasat(MVHSTableau, ⊥, →(α, β), H4) == true
@test alphasat(MVHSTableau, ⊥, →(α, ⊤), H4) == true
@test alphasat(MVHSTableau, ⊥, →(β, ⊥), H4) == true
@test alphasat(MVHSTableau, ⊥, →(β, α), H4) == true
@test alphasat(MVHSTableau, ⊥, →(β, β), H4) == true
@test alphasat(MVHSTableau, ⊥, →(β, ⊤), H4) == true
@test alphasat(MVHSTableau, ⊥, →(⊤, ⊥), H4) == true
@test alphasat(MVHSTableau, ⊥, →(⊤, α), H4) == true
@test alphasat(MVHSTableau, ⊥, →(⊤, β), H4) == true
@test alphasat(MVHSTableau, ⊥, →(⊤, ⊤), H4) == true

@test alphasat(MVHSTableau, α, →(⊥, ⊥), H4) == true
@test alphasat(MVHSTableau, α, →(⊥, α), H4) == true
@test alphasat(MVHSTableau, α, →(⊥, β), H4) == true
@test alphasat(MVHSTableau, α, →(⊥, ⊤), H4) == true
@test alphasat(MVHSTableau, α, →(α, ⊥), H4) == false
@test alphasat(MVHSTableau, α, →(α, α), H4) == true
@test alphasat(MVHSTableau, α, →(α, β), H4) == false
@test alphasat(MVHSTableau, α, →(α, ⊤), H4) == true
@test alphasat(MVHSTableau, α, →(β, ⊥), H4) == true
@test alphasat(MVHSTableau, α, →(β, α), H4) == true
@test alphasat(MVHSTableau, α, →(β, β), H4) == true
@test alphasat(MVHSTableau, α, →(β, ⊤), H4) == true
@test alphasat(MVHSTableau, α, →(⊤, ⊥), H4) == false
@test alphasat(MVHSTableau, α, →(⊤, α), H4) == true
@test alphasat(MVHSTableau, α, →(⊤, β), H4) == false
@test alphasat(MVHSTableau, α, →(⊤, ⊤), H4) == true

@test alphasat(MVHSTableau, β, →(⊥, ⊥), H4) == true
@test alphasat(MVHSTableau, β, →(⊥, α), H4) == true
@test alphasat(MVHSTableau, β, →(⊥, β), H4) == true
@test alphasat(MVHSTableau, β, →(⊥, ⊤), H4) == true
@test alphasat(MVHSTableau, β, →(α, ⊥), H4) == true
@test alphasat(MVHSTableau, β, →(α, α), H4) == true
@test alphasat(MVHSTableau, β, →(α, β), H4) == true
@test alphasat(MVHSTableau, β, →(α, ⊤), H4) == true
@test alphasat(MVHSTableau, β, →(β, ⊥), H4) == false
@test alphasat(MVHSTableau, β, →(β, α), H4) == false
@test alphasat(MVHSTableau, β, →(β, β), H4) == true
@test alphasat(MVHSTableau, β, →(β, ⊤), H4) == true
@test alphasat(MVHSTableau, β, →(⊤, ⊥), H4) == false
@test alphasat(MVHSTableau, β, →(⊤, α), H4) == false
@test alphasat(MVHSTableau, β, →(⊤, β), H4) == true
@test alphasat(MVHSTableau, β, →(⊤, ⊤), H4) == true

@test alphasat(MVHSTableau, ⊤, →(⊥, ⊥), H4) == true
@test alphasat(MVHSTableau, ⊤, →(⊥, α), H4) == true
@test alphasat(MVHSTableau, ⊤, →(⊥, β), H4) == true
@test alphasat(MVHSTableau, ⊤, →(⊥, ⊤), H4) == true
@test alphasat(MVHSTableau, ⊤, →(α, ⊥), H4) == false
@test alphasat(MVHSTableau, ⊤, →(α, α), H4) == true
@test alphasat(MVHSTableau, ⊤, →(α, β), H4) == false
@test alphasat(MVHSTableau, ⊤, →(α, ⊤), H4) == true
@test alphasat(MVHSTableau, ⊤, →(β, ⊥), H4) == false
@test alphasat(MVHSTableau, ⊤, →(β, α), H4) == false
@test alphasat(MVHSTableau, ⊤, →(β, β), H4) == true
@test alphasat(MVHSTableau, ⊤, →(β, ⊤), H4) == true
@test alphasat(MVHSTableau, ⊤, →(⊤, ⊥), H4) == false
@test alphasat(MVHSTableau, ⊤, →(⊤, α), H4) == false
@test alphasat(MVHSTableau, ⊤, →(⊤, β), H4) == false
@test alphasat(MVHSTableau, ⊤, →(⊤, ⊤), H4) == true

@test alphasat(MVHSTableau, ⊥, →(p, ⊥), H4) == true
@test alphasat(MVHSTableau, ⊥, →(p, α), H4) == true
@test alphasat(MVHSTableau, ⊥, →(p, β), H4) == true
@test alphasat(MVHSTableau, ⊥, →(p, ⊤), H4) == true
@test alphasat(MVHSTableau, α, →(p, ⊥), H4) == true
@test alphasat(MVHSTableau, α, →(p, α), H4) == true
@test alphasat(MVHSTableau, α, →(p, β), H4) == true
@test alphasat(MVHSTableau, α, →(p, ⊤), H4) == true
@test alphasat(MVHSTableau, β, →(p, ⊥), H4) == true
@test alphasat(MVHSTableau, β, →(p, α), H4) == true
@test alphasat(MVHSTableau, β, →(p, β), H4) == true
@test alphasat(MVHSTableau, β, →(p, ⊤), H4) == true
@test alphasat(MVHSTableau, ⊤, →(p, ⊥), H4) == true
@test alphasat(MVHSTableau, ⊤, →(p, α), H4) == true
@test alphasat(MVHSTableau, ⊤, →(p, β), H4) == true
@test alphasat(MVHSTableau, ⊤, →(p, ⊤), H4) == true

@test alphasat(MVHSTableau, ⊥, →(⊥, p), H4) == true
@test alphasat(MVHSTableau, ⊥, →(α, p), H4) == true
@test alphasat(MVHSTableau, ⊥, →(β, p), H4) == true
@test alphasat(MVHSTableau, ⊥, →(⊤, p), H4) == true
@test alphasat(MVHSTableau, α, →(⊥, p), H4) == true
@test alphasat(MVHSTableau, α, →(α, p), H4) == true
@test alphasat(MVHSTableau, α, →(β, p), H4) == true
@test alphasat(MVHSTableau, α, →(⊤, p), H4) == true
@test alphasat(MVHSTableau, β, →(⊥, p), H4) == true
@test alphasat(MVHSTableau, β, →(α, p), H4) == true
@test alphasat(MVHSTableau, β, →(β, p), H4) == true
@test alphasat(MVHSTableau, β, →(⊤, p), H4) == true
@test alphasat(MVHSTableau, ⊤, →(⊥, p), H4) == true
@test alphasat(MVHSTableau, ⊤, →(α, p), H4) == true
@test alphasat(MVHSTableau, ⊤, →(β, p), H4) == true
@test alphasat(MVHSTableau, ⊤, →(⊤, p), H4) == true

@test alphasat(MVHSTableau, ⊥, →(p, p), H4)
@test alphasat(MVHSTableau, α, →(p, p), H4)
@test alphasat(MVHSTableau, β, →(p, p), H4)
@test alphasat(MVHSTableau, ⊤, →(p, p), H4)

@test alphasat(MVHSTableau, ⊥, →(p, q), H4)
@test alphasat(MVHSTableau, α, →(p, q), H4)
@test alphasat(MVHSTableau, β, →(p, q), H4)
@test alphasat(MVHSTableau, ⊤, →(p, q), H4)

@test alphasat(MVHSTableau, ⊥, →(q, p), H4)
@test alphasat(MVHSTableau, α, →(q, p), H4)
@test alphasat(MVHSTableau, β, →(q, p), H4)
@test alphasat(MVHSTableau, ⊤, →(q, p), H4)

################################################################################
#### More difficult formulas ###################################################
################################################################################

result = alphasat(MVHSTableau, ⊤, booleantofuzzy(parseformula(
    "(x∨y∨z)∧(x∨y∨¬z)∧(x∨¬y∨z)∧(x∨¬y∨¬z)∧" *
    "(¬x∨y∨z)∧(¬x∨y∨¬z)∧(¬x∨¬y∨z)∧(¬x∨¬y∨¬z)"
)), H4)

if !isnothing(result)
    @test result == false
end

################################################################################
#### Modal cases ###############################################################
################################################################################

result = alphasat(
    MVHSTableau,
    ⊥,
    ∧(diamondA(p), boxA(→(p, ⊥))),
    H4,
    timeout=timeout
)

if !isnothing(result)
    @test result == true
end

result = alphasat(
    MVHSTableau,
    α,
    ∧(diamondA(p), boxA(→(p, ⊥))),
    H4,
    timeout=timeout
)

if !isnothing(result)
    @test result == false
end

result = alphasat(
    MVHSTableau,
    ⊤,
    ∧(diamondA(p), boxA(→(p, ⊥))),
    H4,
    timeout=timeout
)

if !isnothing(result)
    @test result == false
end

################################################################################
#### Example from Fuzzy Sets and Systems 456 (2023) ############################
################################################################################

result = alphasat(
    MVHSTableau,
    α,
    ∧(p, diamondA(q)),
    H4,
    timeout=timeout
)

if !isnothing(result)
    @test result == true
end
