################################################################################
#### G4 ########################################################################
################################################################################

using SoleLogics.ManyValuedLogics: G4
using SoleLogics.ManyValuedLogics: α, β

p, q = Atom.(["p", "q"])

timeout = 30

################################################################################
## Base cases ##################################################################
################################################################################

@test alphasat(MVHSTableau, ⊥, ⊥, G4) == true
@test alphasat(MVHSTableau, ⊥, α, G4) == true
@test alphasat(MVHSTableau, ⊥, β, G4) == true
@test alphasat(MVHSTableau, ⊥, ⊤, G4) == true
@test alphasat(MVHSTableau, α, ⊥, G4) == false
@test alphasat(MVHSTableau, α, α, G4) == true
@test alphasat(MVHSTableau, α, β, G4) == true
@test alphasat(MVHSTableau, α, ⊤, G4) == true
@test alphasat(MVHSTableau, β, ⊥, G4) == false
@test alphasat(MVHSTableau, β, α, G4) == false
@test alphasat(MVHSTableau, β, β, G4) == true
@test alphasat(MVHSTableau, β, ⊤, G4) == true
@test alphasat(MVHSTableau, ⊤, ⊥, G4) == false
@test alphasat(MVHSTableau, ⊤, α, G4) == false
@test alphasat(MVHSTableau, ⊤, β, G4) == false
@test alphasat(MVHSTableau, ⊤, ⊤, G4) == true

@test alphasat(MVHSTableau, ⊥, p, G4) == true
@test alphasat(MVHSTableau, α, p, G4) == true
@test alphasat(MVHSTableau, β, p, G4) == true
@test alphasat(MVHSTableau, ⊤, p, G4) == true

################################################################################
## (Strong) disjuction #########################################################
################################################################################

@test alphasat(MVHSTableau, ⊥, ∨(⊥, ⊥), G4) == true
@test alphasat(MVHSTableau, ⊥, ∨(⊥, α), G4) == true
@test alphasat(MVHSTableau, ⊥, ∨(⊥, β), G4) == true
@test alphasat(MVHSTableau, ⊥, ∨(⊥, ⊤), G4) == true
@test alphasat(MVHSTableau, ⊥, ∨(α, ⊥), G4) == true
@test alphasat(MVHSTableau, ⊥, ∨(α, α), G4) == true
@test alphasat(MVHSTableau, ⊥, ∨(α, β), G4) == true
@test alphasat(MVHSTableau, ⊥, ∨(α, ⊤), G4) == true
@test alphasat(MVHSTableau, ⊥, ∨(β, ⊥), G4) == true
@test alphasat(MVHSTableau, ⊥, ∨(β, α), G4) == true
@test alphasat(MVHSTableau, ⊥, ∨(β, β), G4) == true
@test alphasat(MVHSTableau, ⊥, ∨(β, ⊤), G4) == true
@test alphasat(MVHSTableau, ⊥, ∨(⊤, ⊥), G4) == true
@test alphasat(MVHSTableau, ⊥, ∨(⊤, α), G4) == true
@test alphasat(MVHSTableau, ⊥, ∨(⊤, β), G4) == true
@test alphasat(MVHSTableau, ⊥, ∨(⊤, ⊤), G4) == true

@test alphasat(MVHSTableau, α, ∨(⊥, ⊥), G4) == false
@test alphasat(MVHSTableau, α, ∨(⊥, α), G4) == true
@test alphasat(MVHSTableau, α, ∨(⊥, β), G4) == true
@test alphasat(MVHSTableau, α, ∨(⊥, ⊤), G4) == true
@test alphasat(MVHSTableau, α, ∨(α, ⊥), G4) == true
@test alphasat(MVHSTableau, α, ∨(α, α), G4) == true
@test alphasat(MVHSTableau, α, ∨(α, β), G4) == true
@test alphasat(MVHSTableau, α, ∨(α, ⊤), G4) == true
@test alphasat(MVHSTableau, α, ∨(β, ⊥), G4) == true
@test alphasat(MVHSTableau, α, ∨(β, α), G4) == true
@test alphasat(MVHSTableau, α, ∨(β, β), G4) == true
@test alphasat(MVHSTableau, α, ∨(β, ⊤), G4) == true
@test alphasat(MVHSTableau, α, ∨(⊤, ⊥), G4) == true
@test alphasat(MVHSTableau, α, ∨(⊤, α), G4) == true
@test alphasat(MVHSTableau, α, ∨(⊤, β), G4) == true
@test alphasat(MVHSTableau, α, ∨(⊤, ⊤), G4) == true

@test alphasat(MVHSTableau, β, ∨(⊥, ⊥), G4) == false
@test alphasat(MVHSTableau, β, ∨(⊥, α), G4) == false
@test alphasat(MVHSTableau, β, ∨(⊥, β), G4) == true
@test alphasat(MVHSTableau, β, ∨(⊥, ⊤), G4) == true
@test alphasat(MVHSTableau, β, ∨(α, ⊥), G4) == false
@test alphasat(MVHSTableau, β, ∨(α, α), G4) == false
@test alphasat(MVHSTableau, β, ∨(α, β), G4) == true
@test alphasat(MVHSTableau, β, ∨(α, ⊤), G4) == true
@test alphasat(MVHSTableau, β, ∨(β, ⊥), G4) == true
@test alphasat(MVHSTableau, β, ∨(β, α), G4) == true
@test alphasat(MVHSTableau, β, ∨(β, β), G4) == true
@test alphasat(MVHSTableau, β, ∨(β, ⊤), G4) == true
@test alphasat(MVHSTableau, β, ∨(⊤, ⊥), G4) == true
@test alphasat(MVHSTableau, β, ∨(⊤, α), G4) == true
@test alphasat(MVHSTableau, β, ∨(⊤, β), G4) == true
@test alphasat(MVHSTableau, β, ∨(⊤, ⊤), G4) == true

@test alphasat(MVHSTableau, ⊤, ∨(⊥, ⊥), G4) == false
@test alphasat(MVHSTableau, ⊤, ∨(⊥, α), G4) == false
@test alphasat(MVHSTableau, ⊤, ∨(⊥, β), G4) == false
@test alphasat(MVHSTableau, ⊤, ∨(⊥, ⊤), G4) == true
@test alphasat(MVHSTableau, ⊤, ∨(α, ⊥), G4) == false
@test alphasat(MVHSTableau, ⊤, ∨(α, α), G4) == false
@test alphasat(MVHSTableau, ⊤, ∨(α, β), G4) == false
@test alphasat(MVHSTableau, ⊤, ∨(α, ⊤), G4) == true
@test alphasat(MVHSTableau, ⊤, ∨(β, ⊥), G4) == false
@test alphasat(MVHSTableau, ⊤, ∨(β, α), G4) == false
@test alphasat(MVHSTableau, ⊤, ∨(β, β), G4) == false
@test alphasat(MVHSTableau, ⊤, ∨(β, ⊤), G4) == true
@test alphasat(MVHSTableau, ⊤, ∨(⊤, ⊥), G4) == true
@test alphasat(MVHSTableau, ⊤, ∨(⊤, α), G4) == true
@test alphasat(MVHSTableau, ⊤, ∨(⊤, β), G4) == true
@test alphasat(MVHSTableau, ⊤, ∨(⊤, ⊤), G4) == true

@test alphasat(MVHSTableau, ⊥, ∨(p, ⊥), G4) == true
@test alphasat(MVHSTableau, ⊥, ∨(p, α), G4) == true
@test alphasat(MVHSTableau, ⊥, ∨(p, β), G4) == true
@test alphasat(MVHSTableau, ⊥, ∨(p, ⊤), G4) == true
@test alphasat(MVHSTableau, α, ∨(p, ⊥), G4) == true
@test alphasat(MVHSTableau, α, ∨(p, α), G4) == true
@test alphasat(MVHSTableau, α, ∨(p, β), G4) == true
@test alphasat(MVHSTableau, α, ∨(p, ⊤), G4) == true
@test alphasat(MVHSTableau, β, ∨(p, ⊥), G4) == true
@test alphasat(MVHSTableau, β, ∨(p, α), G4) == true
@test alphasat(MVHSTableau, β, ∨(p, β), G4) == true
@test alphasat(MVHSTableau, β, ∨(p, ⊤), G4) == true
@test alphasat(MVHSTableau, ⊤, ∨(p, ⊥), G4) == true
@test alphasat(MVHSTableau, ⊤, ∨(p, α), G4) == true
@test alphasat(MVHSTableau, ⊤, ∨(p, β), G4) == true
@test alphasat(MVHSTableau, ⊤, ∨(p, ⊤), G4) == true

@test alphasat(MVHSTableau, ⊥, ∨(⊥, p), G4) == true
@test alphasat(MVHSTableau, ⊥, ∨(α, p), G4) == true
@test alphasat(MVHSTableau, ⊥, ∨(β, p), G4) == true
@test alphasat(MVHSTableau, ⊥, ∨(⊤, p), G4) == true
@test alphasat(MVHSTableau, α, ∨(⊥, p), G4) == true
@test alphasat(MVHSTableau, α, ∨(α, p), G4) == true
@test alphasat(MVHSTableau, α, ∨(β, p), G4) == true
@test alphasat(MVHSTableau, α, ∨(⊤, p), G4) == true
@test alphasat(MVHSTableau, β, ∨(⊥, p), G4) == true
@test alphasat(MVHSTableau, β, ∨(α, p), G4) == true
@test alphasat(MVHSTableau, β, ∨(β, p), G4) == true
@test alphasat(MVHSTableau, β, ∨(⊤, p), G4) == true
@test alphasat(MVHSTableau, ⊤, ∨(⊥, p), G4) == true
@test alphasat(MVHSTableau, ⊤, ∨(α, p), G4) == true
@test alphasat(MVHSTableau, ⊤, ∨(β, p), G4) == true
@test alphasat(MVHSTableau, ⊤, ∨(⊤, p), G4) == true

@test alphasat(MVHSTableau, ⊥, ∨(p, p), G4)
@test alphasat(MVHSTableau, α, ∨(p, p), G4)
@test alphasat(MVHSTableau, β, ∨(p, p), G4)
@test alphasat(MVHSTableau, ⊤, ∨(p, p), G4)

@test alphasat(MVHSTableau, ⊥, ∨(p, q), G4)
@test alphasat(MVHSTableau, α, ∨(p, q), G4)
@test alphasat(MVHSTableau, β, ∨(p, q), G4)
@test alphasat(MVHSTableau, ⊤, ∨(p, q), G4)

@test alphasat(MVHSTableau, ⊥, ∨(q, q), G4)
@test alphasat(MVHSTableau, α, ∨(q, q), G4)
@test alphasat(MVHSTableau, β, ∨(q, q), G4)
@test alphasat(MVHSTableau, ⊤, ∨(q, q), G4)

################################################################################
## (Strong) conjunction ########################################################
################################################################################

@test alphasat(MVHSTableau, ⊥, ∧(⊥, ⊥), G4) == true
@test alphasat(MVHSTableau, ⊥, ∧(⊥, α), G4) == true
@test alphasat(MVHSTableau, ⊥, ∧(⊥, β), G4) == true
@test alphasat(MVHSTableau, ⊥, ∧(⊥, ⊤), G4) == true
@test alphasat(MVHSTableau, ⊥, ∧(α, ⊥), G4) == true
@test alphasat(MVHSTableau, ⊥, ∧(α, α), G4) == true
@test alphasat(MVHSTableau, ⊥, ∧(α, β), G4) == true
@test alphasat(MVHSTableau, ⊥, ∧(α, ⊤), G4) == true
@test alphasat(MVHSTableau, ⊥, ∧(β, ⊥), G4) == true
@test alphasat(MVHSTableau, ⊥, ∧(β, α), G4) == true
@test alphasat(MVHSTableau, ⊥, ∧(β, β), G4) == true
@test alphasat(MVHSTableau, ⊥, ∧(β, ⊤), G4) == true
@test alphasat(MVHSTableau, ⊥, ∧(⊤, ⊥), G4) == true
@test alphasat(MVHSTableau, ⊥, ∧(⊤, α), G4) == true
@test alphasat(MVHSTableau, ⊥, ∧(⊤, β), G4) == true
@test alphasat(MVHSTableau, ⊥, ∧(⊤, ⊤), G4) == true

@test alphasat(MVHSTableau, α, ∧(⊥, ⊥), G4) == false
@test alphasat(MVHSTableau, α, ∧(⊥, α), G4) == false
@test alphasat(MVHSTableau, α, ∧(⊥, β), G4) == false
@test alphasat(MVHSTableau, α, ∧(⊥, ⊤), G4) == false
@test alphasat(MVHSTableau, α, ∧(α, ⊥), G4) == false
@test alphasat(MVHSTableau, α, ∧(α, α), G4) == true
@test alphasat(MVHSTableau, α, ∧(α, β), G4) == true
@test alphasat(MVHSTableau, α, ∧(α, ⊤), G4) == true
@test alphasat(MVHSTableau, α, ∧(β, ⊥), G4) == false
@test alphasat(MVHSTableau, α, ∧(β, α), G4) == true
@test alphasat(MVHSTableau, α, ∧(β, β), G4) == true
@test alphasat(MVHSTableau, α, ∧(β, ⊤), G4) == true
@test alphasat(MVHSTableau, α, ∧(⊤, ⊥), G4) == false
@test alphasat(MVHSTableau, α, ∧(⊤, α), G4) == true
@test alphasat(MVHSTableau, α, ∧(⊤, β), G4) == true
@test alphasat(MVHSTableau, α, ∧(⊤, ⊤), G4) == true

@test alphasat(MVHSTableau, β, ∧(⊥, ⊥), G4) == false
@test alphasat(MVHSTableau, β, ∧(⊥, α), G4) == false
@test alphasat(MVHSTableau, β, ∧(⊥, β), G4) == false
@test alphasat(MVHSTableau, β, ∧(⊥, ⊤), G4) == false
@test alphasat(MVHSTableau, β, ∧(α, ⊥), G4) == false
@test alphasat(MVHSTableau, β, ∧(α, α), G4) == false
@test alphasat(MVHSTableau, β, ∧(α, β), G4) == false
@test alphasat(MVHSTableau, β, ∧(α, ⊤), G4) == false
@test alphasat(MVHSTableau, β, ∧(β, ⊥), G4) == false
@test alphasat(MVHSTableau, β, ∧(β, α), G4) == false
@test alphasat(MVHSTableau, β, ∧(β, β), G4) == true
@test alphasat(MVHSTableau, β, ∧(β, ⊤), G4) == true
@test alphasat(MVHSTableau, β, ∧(⊤, ⊥), G4) == false
@test alphasat(MVHSTableau, β, ∧(⊤, α), G4) == false
@test alphasat(MVHSTableau, β, ∧(⊤, β), G4) == true
@test alphasat(MVHSTableau, β, ∧(⊤, ⊤), G4) == true

@test alphasat(MVHSTableau, ⊤, ∧(⊥, ⊥), G4) == false
@test alphasat(MVHSTableau, ⊤, ∧(⊥, α), G4) == false
@test alphasat(MVHSTableau, ⊤, ∧(⊥, β), G4) == false
@test alphasat(MVHSTableau, ⊤, ∧(⊥, ⊤), G4) == false
@test alphasat(MVHSTableau, ⊤, ∧(α, ⊥), G4) == false
@test alphasat(MVHSTableau, ⊤, ∧(α, α), G4) == false
@test alphasat(MVHSTableau, ⊤, ∧(α, β), G4) == false
@test alphasat(MVHSTableau, ⊤, ∧(α, ⊤), G4) == false
@test alphasat(MVHSTableau, ⊤, ∧(β, ⊥), G4) == false
@test alphasat(MVHSTableau, ⊤, ∧(β, α), G4) == false
@test alphasat(MVHSTableau, ⊤, ∧(β, β), G4) == false
@test alphasat(MVHSTableau, ⊤, ∧(β, ⊤), G4) == false
@test alphasat(MVHSTableau, ⊤, ∧(⊤, ⊥), G4) == false
@test alphasat(MVHSTableau, ⊤, ∧(⊤, α), G4) == false
@test alphasat(MVHSTableau, ⊤, ∧(⊤, β), G4) == false
@test alphasat(MVHSTableau, ⊤, ∧(⊤, ⊤), G4) == true

@test alphasat(MVHSTableau, ⊥, ∧(p, ⊥), G4) == true
@test alphasat(MVHSTableau, ⊥, ∧(p, α), G4) == true
@test alphasat(MVHSTableau, ⊥, ∧(p, β), G4) == true
@test alphasat(MVHSTableau, ⊥, ∧(p, ⊤), G4) == true
@test alphasat(MVHSTableau, α, ∧(p, ⊥), G4) == false
@test alphasat(MVHSTableau, α, ∧(p, α), G4) == true
@test alphasat(MVHSTableau, α, ∧(p, β), G4) == true
@test alphasat(MVHSTableau, α, ∧(p, ⊤), G4) == true
@test alphasat(MVHSTableau, β, ∧(p, ⊥), G4) == false
@test alphasat(MVHSTableau, β, ∧(p, α), G4) == false
@test alphasat(MVHSTableau, β, ∧(p, β), G4) == true
@test alphasat(MVHSTableau, β, ∧(p, ⊤), G4) == true
@test alphasat(MVHSTableau, ⊤, ∧(p, ⊥), G4) == false
@test alphasat(MVHSTableau, ⊤, ∧(p, α), G4) == false
@test alphasat(MVHSTableau, ⊤, ∧(p, β), G4) == false
@test alphasat(MVHSTableau, ⊤, ∧(p, ⊤), G4) == true

@test alphasat(MVHSTableau, ⊥, ∧(⊥, p), G4) == true
@test alphasat(MVHSTableau, ⊥, ∧(α, p), G4) == true
@test alphasat(MVHSTableau, ⊥, ∧(β, p), G4) == true
@test alphasat(MVHSTableau, ⊥, ∧(⊤, p), G4) == true
@test alphasat(MVHSTableau, α, ∧(⊥, p), G4) == false
@test alphasat(MVHSTableau, α, ∧(α, p), G4) == true
@test alphasat(MVHSTableau, α, ∧(β, p), G4) == true
@test alphasat(MVHSTableau, α, ∧(⊤, p), G4) == true
@test alphasat(MVHSTableau, β, ∧(⊥, p), G4) == false
@test alphasat(MVHSTableau, β, ∧(α, p), G4) == false
@test alphasat(MVHSTableau, β, ∧(β, p), G4) == true
@test alphasat(MVHSTableau, β, ∧(⊤, p), G4) == true
@test alphasat(MVHSTableau, ⊤, ∧(⊥, p), G4) == false
@test alphasat(MVHSTableau, ⊤, ∧(α, p), G4) == false
@test alphasat(MVHSTableau, ⊤, ∧(β, p), G4) == false
@test alphasat(MVHSTableau, ⊤, ∧(⊤, p), G4) == true

@test alphasat(MVHSTableau, ⊥, ∧(p, p), G4)
@test alphasat(MVHSTableau, α, ∧(p, p), G4)
@test alphasat(MVHSTableau, β, ∧(p, p), G4)
@test alphasat(MVHSTableau, ⊤, ∧(p, p), G4)

@test alphasat(MVHSTableau, ⊥, ∧(p, q), G4)
@test alphasat(MVHSTableau, α, ∧(p, q), G4)
@test alphasat(MVHSTableau, β, ∧(p, q), G4)
@test alphasat(MVHSTableau, ⊤, ∧(p, q), G4)

@test alphasat(MVHSTableau, ⊥, ∧(q, p), G4)
@test alphasat(MVHSTableau, α, ∧(q, p), G4)
@test alphasat(MVHSTableau, β, ∧(q, p), G4)
@test alphasat(MVHSTableau, ⊤, ∧(q, p), G4)

################################################################################
## Implication #################################################################
################################################################################

@test alphasat(MVHSTableau, ⊥, →(⊥, ⊥), G4) == true
@test alphasat(MVHSTableau, ⊥, →(⊥, α), G4) == true
@test alphasat(MVHSTableau, ⊥, →(⊥, β), G4) == true
@test alphasat(MVHSTableau, ⊥, →(⊥, ⊤), G4) == true
@test alphasat(MVHSTableau, ⊥, →(α, ⊥), G4) == true
@test alphasat(MVHSTableau, ⊥, →(α, α), G4) == true
@test alphasat(MVHSTableau, ⊥, →(α, β), G4) == true
@test alphasat(MVHSTableau, ⊥, →(α, ⊤), G4) == true
@test alphasat(MVHSTableau, ⊥, →(β, ⊥), G4) == true
@test alphasat(MVHSTableau, ⊥, →(β, α), G4) == true
@test alphasat(MVHSTableau, ⊥, →(β, β), G4) == true
@test alphasat(MVHSTableau, ⊥, →(β, ⊤), G4) == true
@test alphasat(MVHSTableau, ⊥, →(⊤, ⊥), G4) == true
@test alphasat(MVHSTableau, ⊥, →(⊤, α), G4) == true
@test alphasat(MVHSTableau, ⊥, →(⊤, β), G4) == true
@test alphasat(MVHSTableau, ⊥, →(⊤, ⊤), G4) == true

@test alphasat(MVHSTableau, α, →(⊥, ⊥), G4) == true
@test alphasat(MVHSTableau, α, →(⊥, α), G4) == true
@test alphasat(MVHSTableau, α, →(⊥, β), G4) == true
@test alphasat(MVHSTableau, α, →(⊥, ⊤), G4) == true
@test alphasat(MVHSTableau, α, →(α, ⊥), G4) == false
@test alphasat(MVHSTableau, α, →(α, α), G4) == true
@test alphasat(MVHSTableau, α, →(α, β), G4) == true
@test alphasat(MVHSTableau, α, →(α, ⊤), G4) == true
@test alphasat(MVHSTableau, α, →(β, ⊥), G4) == false
@test alphasat(MVHSTableau, α, →(β, α), G4) == true
@test alphasat(MVHSTableau, α, →(β, β), G4) == true
@test alphasat(MVHSTableau, α, →(β, ⊤), G4) == true
@test alphasat(MVHSTableau, α, →(⊤, ⊥), G4) == false
@test alphasat(MVHSTableau, α, →(⊤, α), G4) == true
@test alphasat(MVHSTableau, α, →(⊤, β), G4) == true
@test alphasat(MVHSTableau, α, →(⊤, ⊤), G4) == true

@test alphasat(MVHSTableau, β, →(⊥, ⊥), G4) == true
@test alphasat(MVHSTableau, β, →(⊥, α), G4) == true
@test alphasat(MVHSTableau, β, →(⊥, β), G4) == true
@test alphasat(MVHSTableau, β, →(⊥, ⊤), G4) == true
@test alphasat(MVHSTableau, β, →(α, ⊥), G4) == false
@test alphasat(MVHSTableau, β, →(α, α), G4) == true
@test alphasat(MVHSTableau, β, →(α, β), G4) == true
@test alphasat(MVHSTableau, β, →(α, ⊤), G4) == true
@test alphasat(MVHSTableau, β, →(β, ⊥), G4) == false
@test alphasat(MVHSTableau, β, →(β, α), G4) == false
@test alphasat(MVHSTableau, β, →(β, β), G4) == true
@test alphasat(MVHSTableau, β, →(β, ⊤), G4) == true
@test alphasat(MVHSTableau, β, →(⊤, ⊥), G4) == false
@test alphasat(MVHSTableau, β, →(⊤, α), G4) == false
@test alphasat(MVHSTableau, β, →(⊤, β), G4) == true
@test alphasat(MVHSTableau, β, →(⊤, ⊤), G4) == true

@test alphasat(MVHSTableau, ⊤, →(⊥, ⊥), G4) == true
@test alphasat(MVHSTableau, ⊤, →(⊥, α), G4) == true
@test alphasat(MVHSTableau, ⊤, →(⊥, β), G4) == true
@test alphasat(MVHSTableau, ⊤, →(⊥, ⊤), G4) == true
@test alphasat(MVHSTableau, ⊤, →(α, ⊥), G4) == false
@test alphasat(MVHSTableau, ⊤, →(α, α), G4) == true
@test alphasat(MVHSTableau, ⊤, →(α, β), G4) == true
@test alphasat(MVHSTableau, ⊤, →(α, ⊤), G4) == true
@test alphasat(MVHSTableau, ⊤, →(β, ⊥), G4) == false
@test alphasat(MVHSTableau, ⊤, →(β, α), G4) == false
@test alphasat(MVHSTableau, ⊤, →(β, β), G4) == true
@test alphasat(MVHSTableau, ⊤, →(β, ⊤), G4) == true
@test alphasat(MVHSTableau, ⊤, →(⊤, ⊥), G4) == false
@test alphasat(MVHSTableau, ⊤, →(⊤, α), G4) == false
@test alphasat(MVHSTableau, ⊤, →(⊤, β), G4) == false
@test alphasat(MVHSTableau, ⊤, →(⊤, ⊤), G4) == true

@test alphasat(MVHSTableau, ⊥, →(p, ⊥), G4) == true
@test alphasat(MVHSTableau, ⊥, →(p, α), G4) == true
@test alphasat(MVHSTableau, ⊥, →(p, β), G4) == true
@test alphasat(MVHSTableau, ⊥, →(p, ⊤), G4) == true
@test alphasat(MVHSTableau, α, →(p, ⊥), G4) == true
@test alphasat(MVHSTableau, α, →(p, α), G4) == true
@test alphasat(MVHSTableau, α, →(p, β), G4) == true
@test alphasat(MVHSTableau, α, →(p, ⊤), G4) == true
@test alphasat(MVHSTableau, β, →(p, ⊥), G4) == true
@test alphasat(MVHSTableau, β, →(p, α), G4) == true
@test alphasat(MVHSTableau, β, →(p, β), G4) == true
@test alphasat(MVHSTableau, β, →(p, ⊤), G4) == true
@test alphasat(MVHSTableau, ⊤, →(p, ⊥), G4) == true
@test alphasat(MVHSTableau, ⊤, →(p, α), G4) == true
@test alphasat(MVHSTableau, ⊤, →(p, β), G4) == true
@test alphasat(MVHSTableau, ⊤, →(p, ⊤), G4) == true

@test alphasat(MVHSTableau, ⊥, →(⊥, p), G4) == true
@test alphasat(MVHSTableau, ⊥, →(α, p), G4) == true
@test alphasat(MVHSTableau, ⊥, →(β, p), G4) == true
@test alphasat(MVHSTableau, ⊥, →(⊤, p), G4) == true
@test alphasat(MVHSTableau, α, →(⊥, p), G4) == true
@test alphasat(MVHSTableau, α, →(α, p), G4) == true
@test alphasat(MVHSTableau, α, →(β, p), G4) == true
@test alphasat(MVHSTableau, α, →(⊤, p), G4) == true
@test alphasat(MVHSTableau, β, →(⊥, p), G4) == true
@test alphasat(MVHSTableau, β, →(α, p), G4) == true
@test alphasat(MVHSTableau, β, →(β, p), G4) == true
@test alphasat(MVHSTableau, β, →(⊤, p), G4) == true
@test alphasat(MVHSTableau, ⊤, →(⊥, p), G4) == true
@test alphasat(MVHSTableau, ⊤, →(α, p), G4) == true
@test alphasat(MVHSTableau, ⊤, →(β, p), G4) == true
@test alphasat(MVHSTableau, ⊤, →(⊤, p), G4) == true

@test alphasat(MVHSTableau, ⊥, →(p, p), G4)
@test alphasat(MVHSTableau, α, →(p, p), G4)
@test alphasat(MVHSTableau, β, →(p, p), G4)
@test alphasat(MVHSTableau, ⊤, →(p, p), G4)

@test alphasat(MVHSTableau, ⊥, →(p, q), G4)
@test alphasat(MVHSTableau, α, →(p, q), G4)
@test alphasat(MVHSTableau, β, →(p, q), G4)
@test alphasat(MVHSTableau, ⊤, →(p, q), G4)

@test alphasat(MVHSTableau, ⊥, →(q, p), G4)
@test alphasat(MVHSTableau, α, →(q, p), G4)
@test alphasat(MVHSTableau, β, →(q, p), G4)
@test alphasat(MVHSTableau, ⊤, →(q, p), G4)

################################################################################
#### More difficult formulas ###################################################
################################################################################

result = alphasat(MVHSTableau, ⊤, booleantofuzzy(parseformula(
    "(x∨y∨z)∧(x∨y∨¬z)∧(x∨¬y∨z)∧(x∨¬y∨¬z)∧" *
    "(¬x∨y∨z)∧(¬x∨y∨¬z)∧(¬x∨¬y∨z)∧(¬x∨¬y∨¬z)"
)), G4, timeout=timeout)

if !isnothing(result)
    @test result == false
end
