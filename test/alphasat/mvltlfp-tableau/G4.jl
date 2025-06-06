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

@test alphasat(MVLTLFPTableau, ⊥, ⊥, G4) == true
@test alphasat(MVLTLFPTableau, ⊥, α, G4) == true
@test alphasat(MVLTLFPTableau, ⊥, β, G4) == true
@test alphasat(MVLTLFPTableau, ⊥, ⊤, G4) == true
@test alphasat(MVLTLFPTableau, α, ⊥, G4) == false
@test alphasat(MVLTLFPTableau, α, α, G4) == true
@test alphasat(MVLTLFPTableau, α, β, G4) == true
@test alphasat(MVLTLFPTableau, α, ⊤, G4) == true
@test alphasat(MVLTLFPTableau, β, ⊥, G4) == false
@test alphasat(MVLTLFPTableau, β, α, G4) == false
@test alphasat(MVLTLFPTableau, β, β, G4) == true
@test alphasat(MVLTLFPTableau, β, ⊤, G4) == true
@test alphasat(MVLTLFPTableau, ⊤, ⊥, G4) == false
@test alphasat(MVLTLFPTableau, ⊤, α, G4) == false
@test alphasat(MVLTLFPTableau, ⊤, β, G4) == false
@test alphasat(MVLTLFPTableau, ⊤, ⊤, G4) == true

@test alphasat(MVLTLFPTableau, ⊥, p, G4) == true
@test alphasat(MVLTLFPTableau, α, p, G4) == true
@test alphasat(MVLTLFPTableau, β, p, G4) == true
@test alphasat(MVLTLFPTableau, ⊤, p, G4) == true

################################################################################
## (Strong) disjuction #########################################################
################################################################################

@test alphasat(MVLTLFPTableau, ⊥, ∨(⊥, ⊥), G4) == true
@test alphasat(MVLTLFPTableau, ⊥, ∨(⊥, α), G4) == true
@test alphasat(MVLTLFPTableau, ⊥, ∨(⊥, β), G4) == true
@test alphasat(MVLTLFPTableau, ⊥, ∨(⊥, ⊤), G4) == true
@test alphasat(MVLTLFPTableau, ⊥, ∨(α, ⊥), G4) == true
@test alphasat(MVLTLFPTableau, ⊥, ∨(α, α), G4) == true
@test alphasat(MVLTLFPTableau, ⊥, ∨(α, β), G4) == true
@test alphasat(MVLTLFPTableau, ⊥, ∨(α, ⊤), G4) == true
@test alphasat(MVLTLFPTableau, ⊥, ∨(β, ⊥), G4) == true
@test alphasat(MVLTLFPTableau, ⊥, ∨(β, α), G4) == true
@test alphasat(MVLTLFPTableau, ⊥, ∨(β, β), G4) == true
@test alphasat(MVLTLFPTableau, ⊥, ∨(β, ⊤), G4) == true
@test alphasat(MVLTLFPTableau, ⊥, ∨(⊤, ⊥), G4) == true
@test alphasat(MVLTLFPTableau, ⊥, ∨(⊤, α), G4) == true
@test alphasat(MVLTLFPTableau, ⊥, ∨(⊤, β), G4) == true
@test alphasat(MVLTLFPTableau, ⊥, ∨(⊤, ⊤), G4) == true

@test alphasat(MVLTLFPTableau, α, ∨(⊥, ⊥), G4) == false
@test alphasat(MVLTLFPTableau, α, ∨(⊥, α), G4) == true
@test alphasat(MVLTLFPTableau, α, ∨(⊥, β), G4) == true
@test alphasat(MVLTLFPTableau, α, ∨(⊥, ⊤), G4) == true
@test alphasat(MVLTLFPTableau, α, ∨(α, ⊥), G4) == true
@test alphasat(MVLTLFPTableau, α, ∨(α, α), G4) == true
@test alphasat(MVLTLFPTableau, α, ∨(α, β), G4) == true
@test alphasat(MVLTLFPTableau, α, ∨(α, ⊤), G4) == true
@test alphasat(MVLTLFPTableau, α, ∨(β, ⊥), G4) == true
@test alphasat(MVLTLFPTableau, α, ∨(β, α), G4) == true
@test alphasat(MVLTLFPTableau, α, ∨(β, β), G4) == true
@test alphasat(MVLTLFPTableau, α, ∨(β, ⊤), G4) == true
@test alphasat(MVLTLFPTableau, α, ∨(⊤, ⊥), G4) == true
@test alphasat(MVLTLFPTableau, α, ∨(⊤, α), G4) == true
@test alphasat(MVLTLFPTableau, α, ∨(⊤, β), G4) == true
@test alphasat(MVLTLFPTableau, α, ∨(⊤, ⊤), G4) == true

@test alphasat(MVLTLFPTableau, β, ∨(⊥, ⊥), G4) == false
@test alphasat(MVLTLFPTableau, β, ∨(⊥, α), G4) == false
@test alphasat(MVLTLFPTableau, β, ∨(⊥, β), G4) == true
@test alphasat(MVLTLFPTableau, β, ∨(⊥, ⊤), G4) == true
@test alphasat(MVLTLFPTableau, β, ∨(α, ⊥), G4) == false
@test alphasat(MVLTLFPTableau, β, ∨(α, α), G4) == false
@test alphasat(MVLTLFPTableau, β, ∨(α, β), G4) == true
@test alphasat(MVLTLFPTableau, β, ∨(α, ⊤), G4) == true
@test alphasat(MVLTLFPTableau, β, ∨(β, ⊥), G4) == true
@test alphasat(MVLTLFPTableau, β, ∨(β, α), G4) == true
@test alphasat(MVLTLFPTableau, β, ∨(β, β), G4) == true
@test alphasat(MVLTLFPTableau, β, ∨(β, ⊤), G4) == true
@test alphasat(MVLTLFPTableau, β, ∨(⊤, ⊥), G4) == true
@test alphasat(MVLTLFPTableau, β, ∨(⊤, α), G4) == true
@test alphasat(MVLTLFPTableau, β, ∨(⊤, β), G4) == true
@test alphasat(MVLTLFPTableau, β, ∨(⊤, ⊤), G4) == true

@test alphasat(MVLTLFPTableau, ⊤, ∨(⊥, ⊥), G4) == false
@test alphasat(MVLTLFPTableau, ⊤, ∨(⊥, α), G4) == false
@test alphasat(MVLTLFPTableau, ⊤, ∨(⊥, β), G4) == false
@test alphasat(MVLTLFPTableau, ⊤, ∨(⊥, ⊤), G4) == true
@test alphasat(MVLTLFPTableau, ⊤, ∨(α, ⊥), G4) == false
@test alphasat(MVLTLFPTableau, ⊤, ∨(α, α), G4) == false
@test alphasat(MVLTLFPTableau, ⊤, ∨(α, β), G4) == false
@test alphasat(MVLTLFPTableau, ⊤, ∨(α, ⊤), G4) == true
@test alphasat(MVLTLFPTableau, ⊤, ∨(β, ⊥), G4) == false
@test alphasat(MVLTLFPTableau, ⊤, ∨(β, α), G4) == false
@test alphasat(MVLTLFPTableau, ⊤, ∨(β, β), G4) == false
@test alphasat(MVLTLFPTableau, ⊤, ∨(β, ⊤), G4) == true
@test alphasat(MVLTLFPTableau, ⊤, ∨(⊤, ⊥), G4) == true
@test alphasat(MVLTLFPTableau, ⊤, ∨(⊤, α), G4) == true
@test alphasat(MVLTLFPTableau, ⊤, ∨(⊤, β), G4) == true
@test alphasat(MVLTLFPTableau, ⊤, ∨(⊤, ⊤), G4) == true

@test alphasat(MVLTLFPTableau, ⊥, ∨(p, ⊥), G4) == true
@test alphasat(MVLTLFPTableau, ⊥, ∨(p, α), G4) == true
@test alphasat(MVLTLFPTableau, ⊥, ∨(p, β), G4) == true
@test alphasat(MVLTLFPTableau, ⊥, ∨(p, ⊤), G4) == true
@test alphasat(MVLTLFPTableau, α, ∨(p, ⊥), G4) == true
@test alphasat(MVLTLFPTableau, α, ∨(p, α), G4) == true
@test alphasat(MVLTLFPTableau, α, ∨(p, β), G4) == true
@test alphasat(MVLTLFPTableau, α, ∨(p, ⊤), G4) == true
@test alphasat(MVLTLFPTableau, β, ∨(p, ⊥), G4) == true
@test alphasat(MVLTLFPTableau, β, ∨(p, α), G4) == true
@test alphasat(MVLTLFPTableau, β, ∨(p, β), G4) == true
@test alphasat(MVLTLFPTableau, β, ∨(p, ⊤), G4) == true
@test alphasat(MVLTLFPTableau, ⊤, ∨(p, ⊥), G4) == true
@test alphasat(MVLTLFPTableau, ⊤, ∨(p, α), G4) == true
@test alphasat(MVLTLFPTableau, ⊤, ∨(p, β), G4) == true
@test alphasat(MVLTLFPTableau, ⊤, ∨(p, ⊤), G4) == true

@test alphasat(MVLTLFPTableau, ⊥, ∨(⊥, p), G4) == true
@test alphasat(MVLTLFPTableau, ⊥, ∨(α, p), G4) == true
@test alphasat(MVLTLFPTableau, ⊥, ∨(β, p), G4) == true
@test alphasat(MVLTLFPTableau, ⊥, ∨(⊤, p), G4) == true
@test alphasat(MVLTLFPTableau, α, ∨(⊥, p), G4) == true
@test alphasat(MVLTLFPTableau, α, ∨(α, p), G4) == true
@test alphasat(MVLTLFPTableau, α, ∨(β, p), G4) == true
@test alphasat(MVLTLFPTableau, α, ∨(⊤, p), G4) == true
@test alphasat(MVLTLFPTableau, β, ∨(⊥, p), G4) == true
@test alphasat(MVLTLFPTableau, β, ∨(α, p), G4) == true
@test alphasat(MVLTLFPTableau, β, ∨(β, p), G4) == true
@test alphasat(MVLTLFPTableau, β, ∨(⊤, p), G4) == true
@test alphasat(MVLTLFPTableau, ⊤, ∨(⊥, p), G4) == true
@test alphasat(MVLTLFPTableau, ⊤, ∨(α, p), G4) == true
@test alphasat(MVLTLFPTableau, ⊤, ∨(β, p), G4) == true
@test alphasat(MVLTLFPTableau, ⊤, ∨(⊤, p), G4) == true

@test alphasat(MVLTLFPTableau, ⊥, ∨(p, p), G4)
@test alphasat(MVLTLFPTableau, α, ∨(p, p), G4)
@test alphasat(MVLTLFPTableau, β, ∨(p, p), G4)
@test alphasat(MVLTLFPTableau, ⊤, ∨(p, p), G4)

@test alphasat(MVLTLFPTableau, ⊥, ∨(p, q), G4)
@test alphasat(MVLTLFPTableau, α, ∨(p, q), G4)
@test alphasat(MVLTLFPTableau, β, ∨(p, q), G4)
@test alphasat(MVLTLFPTableau, ⊤, ∨(p, q), G4)

@test alphasat(MVLTLFPTableau, ⊥, ∨(q, q), G4)
@test alphasat(MVLTLFPTableau, α, ∨(q, q), G4)
@test alphasat(MVLTLFPTableau, β, ∨(q, q), G4)
@test alphasat(MVLTLFPTableau, ⊤, ∨(q, q), G4)

################################################################################
## (Strong) conjunction ########################################################
################################################################################

@test alphasat(MVLTLFPTableau, ⊥, ∧(⊥, ⊥), G4) == true
@test alphasat(MVLTLFPTableau, ⊥, ∧(⊥, α), G4) == true
@test alphasat(MVLTLFPTableau, ⊥, ∧(⊥, β), G4) == true
@test alphasat(MVLTLFPTableau, ⊥, ∧(⊥, ⊤), G4) == true
@test alphasat(MVLTLFPTableau, ⊥, ∧(α, ⊥), G4) == true
@test alphasat(MVLTLFPTableau, ⊥, ∧(α, α), G4) == true
@test alphasat(MVLTLFPTableau, ⊥, ∧(α, β), G4) == true
@test alphasat(MVLTLFPTableau, ⊥, ∧(α, ⊤), G4) == true
@test alphasat(MVLTLFPTableau, ⊥, ∧(β, ⊥), G4) == true
@test alphasat(MVLTLFPTableau, ⊥, ∧(β, α), G4) == true
@test alphasat(MVLTLFPTableau, ⊥, ∧(β, β), G4) == true
@test alphasat(MVLTLFPTableau, ⊥, ∧(β, ⊤), G4) == true
@test alphasat(MVLTLFPTableau, ⊥, ∧(⊤, ⊥), G4) == true
@test alphasat(MVLTLFPTableau, ⊥, ∧(⊤, α), G4) == true
@test alphasat(MVLTLFPTableau, ⊥, ∧(⊤, β), G4) == true
@test alphasat(MVLTLFPTableau, ⊥, ∧(⊤, ⊤), G4) == true

@test alphasat(MVLTLFPTableau, α, ∧(⊥, ⊥), G4) == false
@test alphasat(MVLTLFPTableau, α, ∧(⊥, α), G4) == false
@test alphasat(MVLTLFPTableau, α, ∧(⊥, β), G4) == false
@test alphasat(MVLTLFPTableau, α, ∧(⊥, ⊤), G4) == false
@test alphasat(MVLTLFPTableau, α, ∧(α, ⊥), G4) == false
@test alphasat(MVLTLFPTableau, α, ∧(α, α), G4) == true
@test alphasat(MVLTLFPTableau, α, ∧(α, β), G4) == true
@test alphasat(MVLTLFPTableau, α, ∧(α, ⊤), G4) == true
@test alphasat(MVLTLFPTableau, α, ∧(β, ⊥), G4) == false
@test alphasat(MVLTLFPTableau, α, ∧(β, α), G4) == true
@test alphasat(MVLTLFPTableau, α, ∧(β, β), G4) == true
@test alphasat(MVLTLFPTableau, α, ∧(β, ⊤), G4) == true
@test alphasat(MVLTLFPTableau, α, ∧(⊤, ⊥), G4) == false
@test alphasat(MVLTLFPTableau, α, ∧(⊤, α), G4) == true
@test alphasat(MVLTLFPTableau, α, ∧(⊤, β), G4) == true
@test alphasat(MVLTLFPTableau, α, ∧(⊤, ⊤), G4) == true

@test alphasat(MVLTLFPTableau, β, ∧(⊥, ⊥), G4) == false
@test alphasat(MVLTLFPTableau, β, ∧(⊥, α), G4) == false
@test alphasat(MVLTLFPTableau, β, ∧(⊥, β), G4) == false
@test alphasat(MVLTLFPTableau, β, ∧(⊥, ⊤), G4) == false
@test alphasat(MVLTLFPTableau, β, ∧(α, ⊥), G4) == false
@test alphasat(MVLTLFPTableau, β, ∧(α, α), G4) == false
@test alphasat(MVLTLFPTableau, β, ∧(α, β), G4) == false
@test alphasat(MVLTLFPTableau, β, ∧(α, ⊤), G4) == false
@test alphasat(MVLTLFPTableau, β, ∧(β, ⊥), G4) == false
@test alphasat(MVLTLFPTableau, β, ∧(β, α), G4) == false
@test alphasat(MVLTLFPTableau, β, ∧(β, β), G4) == true
@test alphasat(MVLTLFPTableau, β, ∧(β, ⊤), G4) == true
@test alphasat(MVLTLFPTableau, β, ∧(⊤, ⊥), G4) == false
@test alphasat(MVLTLFPTableau, β, ∧(⊤, α), G4) == false
@test alphasat(MVLTLFPTableau, β, ∧(⊤, β), G4) == true
@test alphasat(MVLTLFPTableau, β, ∧(⊤, ⊤), G4) == true

@test alphasat(MVLTLFPTableau, ⊤, ∧(⊥, ⊥), G4) == false
@test alphasat(MVLTLFPTableau, ⊤, ∧(⊥, α), G4) == false
@test alphasat(MVLTLFPTableau, ⊤, ∧(⊥, β), G4) == false
@test alphasat(MVLTLFPTableau, ⊤, ∧(⊥, ⊤), G4) == false
@test alphasat(MVLTLFPTableau, ⊤, ∧(α, ⊥), G4) == false
@test alphasat(MVLTLFPTableau, ⊤, ∧(α, α), G4) == false
@test alphasat(MVLTLFPTableau, ⊤, ∧(α, β), G4) == false
@test alphasat(MVLTLFPTableau, ⊤, ∧(α, ⊤), G4) == false
@test alphasat(MVLTLFPTableau, ⊤, ∧(β, ⊥), G4) == false
@test alphasat(MVLTLFPTableau, ⊤, ∧(β, α), G4) == false
@test alphasat(MVLTLFPTableau, ⊤, ∧(β, β), G4) == false
@test alphasat(MVLTLFPTableau, ⊤, ∧(β, ⊤), G4) == false
@test alphasat(MVLTLFPTableau, ⊤, ∧(⊤, ⊥), G4) == false
@test alphasat(MVLTLFPTableau, ⊤, ∧(⊤, α), G4) == false
@test alphasat(MVLTLFPTableau, ⊤, ∧(⊤, β), G4) == false
@test alphasat(MVLTLFPTableau, ⊤, ∧(⊤, ⊤), G4) == true

@test alphasat(MVLTLFPTableau, ⊥, ∧(p, ⊥), G4) == true
@test alphasat(MVLTLFPTableau, ⊥, ∧(p, α), G4) == true
@test alphasat(MVLTLFPTableau, ⊥, ∧(p, β), G4) == true
@test alphasat(MVLTLFPTableau, ⊥, ∧(p, ⊤), G4) == true
@test alphasat(MVLTLFPTableau, α, ∧(p, ⊥), G4) == false
@test alphasat(MVLTLFPTableau, α, ∧(p, α), G4) == true
@test alphasat(MVLTLFPTableau, α, ∧(p, β), G4) == true
@test alphasat(MVLTLFPTableau, α, ∧(p, ⊤), G4) == true
@test alphasat(MVLTLFPTableau, β, ∧(p, ⊥), G4) == false
@test alphasat(MVLTLFPTableau, β, ∧(p, α), G4) == false
@test alphasat(MVLTLFPTableau, β, ∧(p, β), G4) == true
@test alphasat(MVLTLFPTableau, β, ∧(p, ⊤), G4) == true
@test alphasat(MVLTLFPTableau, ⊤, ∧(p, ⊥), G4) == false
@test alphasat(MVLTLFPTableau, ⊤, ∧(p, α), G4) == false
@test alphasat(MVLTLFPTableau, ⊤, ∧(p, β), G4) == false
@test alphasat(MVLTLFPTableau, ⊤, ∧(p, ⊤), G4) == true

@test alphasat(MVLTLFPTableau, ⊥, ∧(⊥, p), G4) == true
@test alphasat(MVLTLFPTableau, ⊥, ∧(α, p), G4) == true
@test alphasat(MVLTLFPTableau, ⊥, ∧(β, p), G4) == true
@test alphasat(MVLTLFPTableau, ⊥, ∧(⊤, p), G4) == true
@test alphasat(MVLTLFPTableau, α, ∧(⊥, p), G4) == false
@test alphasat(MVLTLFPTableau, α, ∧(α, p), G4) == true
@test alphasat(MVLTLFPTableau, α, ∧(β, p), G4) == true
@test alphasat(MVLTLFPTableau, α, ∧(⊤, p), G4) == true
@test alphasat(MVLTLFPTableau, β, ∧(⊥, p), G4) == false
@test alphasat(MVLTLFPTableau, β, ∧(α, p), G4) == false
@test alphasat(MVLTLFPTableau, β, ∧(β, p), G4) == true
@test alphasat(MVLTLFPTableau, β, ∧(⊤, p), G4) == true
@test alphasat(MVLTLFPTableau, ⊤, ∧(⊥, p), G4) == false
@test alphasat(MVLTLFPTableau, ⊤, ∧(α, p), G4) == false
@test alphasat(MVLTLFPTableau, ⊤, ∧(β, p), G4) == false
@test alphasat(MVLTLFPTableau, ⊤, ∧(⊤, p), G4) == true

@test alphasat(MVLTLFPTableau, ⊥, ∧(p, p), G4)
@test alphasat(MVLTLFPTableau, α, ∧(p, p), G4)
@test alphasat(MVLTLFPTableau, β, ∧(p, p), G4)
@test alphasat(MVLTLFPTableau, ⊤, ∧(p, p), G4)

@test alphasat(MVLTLFPTableau, ⊥, ∧(p, q), G4)
@test alphasat(MVLTLFPTableau, α, ∧(p, q), G4)
@test alphasat(MVLTLFPTableau, β, ∧(p, q), G4)
@test alphasat(MVLTLFPTableau, ⊤, ∧(p, q), G4)

@test alphasat(MVLTLFPTableau, ⊥, ∧(q, p), G4)
@test alphasat(MVLTLFPTableau, α, ∧(q, p), G4)
@test alphasat(MVLTLFPTableau, β, ∧(q, p), G4)
@test alphasat(MVLTLFPTableau, ⊤, ∧(q, p), G4)

################################################################################
## Implication #################################################################
################################################################################

@test alphasat(MVLTLFPTableau, ⊥, →(⊥, ⊥), G4) == true
@test alphasat(MVLTLFPTableau, ⊥, →(⊥, α), G4) == true
@test alphasat(MVLTLFPTableau, ⊥, →(⊥, β), G4) == true
@test alphasat(MVLTLFPTableau, ⊥, →(⊥, ⊤), G4) == true
@test alphasat(MVLTLFPTableau, ⊥, →(α, ⊥), G4) == true
@test alphasat(MVLTLFPTableau, ⊥, →(α, α), G4) == true
@test alphasat(MVLTLFPTableau, ⊥, →(α, β), G4) == true
@test alphasat(MVLTLFPTableau, ⊥, →(α, ⊤), G4) == true
@test alphasat(MVLTLFPTableau, ⊥, →(β, ⊥), G4) == true
@test alphasat(MVLTLFPTableau, ⊥, →(β, α), G4) == true
@test alphasat(MVLTLFPTableau, ⊥, →(β, β), G4) == true
@test alphasat(MVLTLFPTableau, ⊥, →(β, ⊤), G4) == true
@test alphasat(MVLTLFPTableau, ⊥, →(⊤, ⊥), G4) == true
@test alphasat(MVLTLFPTableau, ⊥, →(⊤, α), G4) == true
@test alphasat(MVLTLFPTableau, ⊥, →(⊤, β), G4) == true
@test alphasat(MVLTLFPTableau, ⊥, →(⊤, ⊤), G4) == true

@test alphasat(MVLTLFPTableau, α, →(⊥, ⊥), G4) == true
@test alphasat(MVLTLFPTableau, α, →(⊥, α), G4) == true
@test alphasat(MVLTLFPTableau, α, →(⊥, β), G4) == true
@test alphasat(MVLTLFPTableau, α, →(⊥, ⊤), G4) == true
@test alphasat(MVLTLFPTableau, α, →(α, ⊥), G4) == false
@test alphasat(MVLTLFPTableau, α, →(α, α), G4) == true
@test alphasat(MVLTLFPTableau, α, →(α, β), G4) == true
@test alphasat(MVLTLFPTableau, α, →(α, ⊤), G4) == true
@test alphasat(MVLTLFPTableau, α, →(β, ⊥), G4) == false
@test alphasat(MVLTLFPTableau, α, →(β, α), G4) == true
@test alphasat(MVLTLFPTableau, α, →(β, β), G4) == true
@test alphasat(MVLTLFPTableau, α, →(β, ⊤), G4) == true
@test alphasat(MVLTLFPTableau, α, →(⊤, ⊥), G4) == false
@test alphasat(MVLTLFPTableau, α, →(⊤, α), G4) == true
@test alphasat(MVLTLFPTableau, α, →(⊤, β), G4) == true
@test alphasat(MVLTLFPTableau, α, →(⊤, ⊤), G4) == true

@test alphasat(MVLTLFPTableau, β, →(⊥, ⊥), G4) == true
@test alphasat(MVLTLFPTableau, β, →(⊥, α), G4) == true
@test alphasat(MVLTLFPTableau, β, →(⊥, β), G4) == true
@test alphasat(MVLTLFPTableau, β, →(⊥, ⊤), G4) == true
@test alphasat(MVLTLFPTableau, β, →(α, ⊥), G4) == false
@test alphasat(MVLTLFPTableau, β, →(α, α), G4) == true
@test alphasat(MVLTLFPTableau, β, →(α, β), G4) == true
@test alphasat(MVLTLFPTableau, β, →(α, ⊤), G4) == true
@test alphasat(MVLTLFPTableau, β, →(β, ⊥), G4) == false
@test alphasat(MVLTLFPTableau, β, →(β, α), G4) == false
@test alphasat(MVLTLFPTableau, β, →(β, β), G4) == true
@test alphasat(MVLTLFPTableau, β, →(β, ⊤), G4) == true
@test alphasat(MVLTLFPTableau, β, →(⊤, ⊥), G4) == false
@test alphasat(MVLTLFPTableau, β, →(⊤, α), G4) == false
@test alphasat(MVLTLFPTableau, β, →(⊤, β), G4) == true
@test alphasat(MVLTLFPTableau, β, →(⊤, ⊤), G4) == true

@test alphasat(MVLTLFPTableau, ⊤, →(⊥, ⊥), G4) == true
@test alphasat(MVLTLFPTableau, ⊤, →(⊥, α), G4) == true
@test alphasat(MVLTLFPTableau, ⊤, →(⊥, β), G4) == true
@test alphasat(MVLTLFPTableau, ⊤, →(⊥, ⊤), G4) == true
@test alphasat(MVLTLFPTableau, ⊤, →(α, ⊥), G4) == false
@test alphasat(MVLTLFPTableau, ⊤, →(α, α), G4) == true
@test alphasat(MVLTLFPTableau, ⊤, →(α, β), G4) == true
@test alphasat(MVLTLFPTableau, ⊤, →(α, ⊤), G4) == true
@test alphasat(MVLTLFPTableau, ⊤, →(β, ⊥), G4) == false
@test alphasat(MVLTLFPTableau, ⊤, →(β, α), G4) == false
@test alphasat(MVLTLFPTableau, ⊤, →(β, β), G4) == true
@test alphasat(MVLTLFPTableau, ⊤, →(β, ⊤), G4) == true
@test alphasat(MVLTLFPTableau, ⊤, →(⊤, ⊥), G4) == false
@test alphasat(MVLTLFPTableau, ⊤, →(⊤, α), G4) == false
@test alphasat(MVLTLFPTableau, ⊤, →(⊤, β), G4) == false
@test alphasat(MVLTLFPTableau, ⊤, →(⊤, ⊤), G4) == true

@test alphasat(MVLTLFPTableau, ⊥, →(p, ⊥), G4) == true
@test alphasat(MVLTLFPTableau, ⊥, →(p, α), G4) == true
@test alphasat(MVLTLFPTableau, ⊥, →(p, β), G4) == true
@test alphasat(MVLTLFPTableau, ⊥, →(p, ⊤), G4) == true
@test alphasat(MVLTLFPTableau, α, →(p, ⊥), G4) == true
@test alphasat(MVLTLFPTableau, α, →(p, α), G4) == true
@test alphasat(MVLTLFPTableau, α, →(p, β), G4) == true
@test alphasat(MVLTLFPTableau, α, →(p, ⊤), G4) == true
@test alphasat(MVLTLFPTableau, β, →(p, ⊥), G4) == true
@test alphasat(MVLTLFPTableau, β, →(p, α), G4) == true
@test alphasat(MVLTLFPTableau, β, →(p, β), G4) == true
@test alphasat(MVLTLFPTableau, β, →(p, ⊤), G4) == true
@test alphasat(MVLTLFPTableau, ⊤, →(p, ⊥), G4) == true
@test alphasat(MVLTLFPTableau, ⊤, →(p, α), G4) == true
@test alphasat(MVLTLFPTableau, ⊤, →(p, β), G4) == true
@test alphasat(MVLTLFPTableau, ⊤, →(p, ⊤), G4) == true

@test alphasat(MVLTLFPTableau, ⊥, →(⊥, p), G4) == true
@test alphasat(MVLTLFPTableau, ⊥, →(α, p), G4) == true
@test alphasat(MVLTLFPTableau, ⊥, →(β, p), G4) == true
@test alphasat(MVLTLFPTableau, ⊥, →(⊤, p), G4) == true
@test alphasat(MVLTLFPTableau, α, →(⊥, p), G4) == true
@test alphasat(MVLTLFPTableau, α, →(α, p), G4) == true
@test alphasat(MVLTLFPTableau, α, →(β, p), G4) == true
@test alphasat(MVLTLFPTableau, α, →(⊤, p), G4) == true
@test alphasat(MVLTLFPTableau, β, →(⊥, p), G4) == true
@test alphasat(MVLTLFPTableau, β, →(α, p), G4) == true
@test alphasat(MVLTLFPTableau, β, →(β, p), G4) == true
@test alphasat(MVLTLFPTableau, β, →(⊤, p), G4) == true
@test alphasat(MVLTLFPTableau, ⊤, →(⊥, p), G4) == true
@test alphasat(MVLTLFPTableau, ⊤, →(α, p), G4) == true
@test alphasat(MVLTLFPTableau, ⊤, →(β, p), G4) == true
@test alphasat(MVLTLFPTableau, ⊤, →(⊤, p), G4) == true

@test alphasat(MVLTLFPTableau, ⊥, →(p, p), G4)
@test alphasat(MVLTLFPTableau, α, →(p, p), G4)
@test alphasat(MVLTLFPTableau, β, →(p, p), G4)
@test alphasat(MVLTLFPTableau, ⊤, →(p, p), G4)

@test alphasat(MVLTLFPTableau, ⊥, →(p, q), G4)
@test alphasat(MVLTLFPTableau, α, →(p, q), G4)
@test alphasat(MVLTLFPTableau, β, →(p, q), G4)
@test alphasat(MVLTLFPTableau, ⊤, →(p, q), G4)

@test alphasat(MVLTLFPTableau, ⊥, →(q, p), G4)
@test alphasat(MVLTLFPTableau, α, →(q, p), G4)
@test alphasat(MVLTLFPTableau, β, →(q, p), G4)
@test alphasat(MVLTLFPTableau, ⊤, →(q, p), G4)

################################################################################
#### More difficult formulas ###################################################
################################################################################

result = alphasat(MVLTLFPTableau, ⊤, booleantofuzzy(parseformula(
    "(x∨y∨z)∧(x∨y∨¬z)∧(x∨¬y∨z)∧(x∨¬y∨¬z)∧" *
    "(¬x∨y∨z)∧(¬x∨y∨¬z)∧(¬x∨¬y∨z)∧(¬x∨¬y∨¬z)"
)), G4, timeout=timeout)

if !isnothing(result)
    @test result == false
end
