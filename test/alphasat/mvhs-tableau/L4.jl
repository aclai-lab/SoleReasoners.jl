################################################################################
#### Ł4 ########################################################################
################################################################################

using SoleLogics.ManyValuedLogics: Ł4
using SoleLogics.ManyValuedLogics: α, β

p, q = Atom.(["p", "q"])

timeout = 10

################################################################################
## Base cases ##################################################################
################################################################################

@test alphasat(MVHSTableau, ⊥, ⊥, Ł4) == true
@test alphasat(MVHSTableau, ⊥, α, Ł4) == true
@test alphasat(MVHSTableau, ⊥, β, Ł4) == true
@test alphasat(MVHSTableau, ⊥, ⊤, Ł4) == true
@test alphasat(MVHSTableau, α, ⊥, Ł4) == false
@test alphasat(MVHSTableau, α, α, Ł4) == true
@test alphasat(MVHSTableau, α, β, Ł4) == true
@test alphasat(MVHSTableau, α, ⊤, Ł4) == true
@test alphasat(MVHSTableau, β, ⊥, Ł4) == false
@test alphasat(MVHSTableau, β, α, Ł4) == false
@test alphasat(MVHSTableau, β, β, Ł4) == true
@test alphasat(MVHSTableau, β, ⊤, Ł4) == true
@test alphasat(MVHSTableau, ⊤, ⊥, Ł4) == false
@test alphasat(MVHSTableau, ⊤, α, Ł4) == false
@test alphasat(MVHSTableau, ⊤, β, Ł4) == false
@test alphasat(MVHSTableau, ⊤, ⊤, Ł4) == true

@test alphasat(MVHSTableau, ⊥, p, Ł4) == true
@test alphasat(MVHSTableau, α, p, Ł4) == true
@test alphasat(MVHSTableau, β, p, Ł4) == true
@test alphasat(MVHSTableau, ⊤, p, Ł4) == true

################################################################################
## (Strong) disjuction #########################################################
################################################################################

@test alphasat(MVHSTableau, ⊥, ∨(⊥, ⊥), Ł4) == true
@test alphasat(MVHSTableau, ⊥, ∨(⊥, α), Ł4) == true
@test alphasat(MVHSTableau, ⊥, ∨(⊥, β), Ł4) == true
@test alphasat(MVHSTableau, ⊥, ∨(⊥, ⊤), Ł4) == true
@test alphasat(MVHSTableau, ⊥, ∨(α, ⊥), Ł4) == true
@test alphasat(MVHSTableau, ⊥, ∨(α, α), Ł4) == true
@test alphasat(MVHSTableau, ⊥, ∨(α, β), Ł4) == true
@test alphasat(MVHSTableau, ⊥, ∨(α, ⊤), Ł4) == true
@test alphasat(MVHSTableau, ⊥, ∨(β, ⊥), Ł4) == true
@test alphasat(MVHSTableau, ⊥, ∨(β, α), Ł4) == true
@test alphasat(MVHSTableau, ⊥, ∨(β, β), Ł4) == true
@test alphasat(MVHSTableau, ⊥, ∨(β, ⊤), Ł4) == true
@test alphasat(MVHSTableau, ⊥, ∨(⊤, ⊥), Ł4) == true
@test alphasat(MVHSTableau, ⊥, ∨(⊤, α), Ł4) == true
@test alphasat(MVHSTableau, ⊥, ∨(⊤, β), Ł4) == true
@test alphasat(MVHSTableau, ⊥, ∨(⊤, ⊤), Ł4) == true

@test alphasat(MVHSTableau, α, ∨(⊥, ⊥), Ł4) == false
@test alphasat(MVHSTableau, α, ∨(⊥, α), Ł4) == true
@test alphasat(MVHSTableau, α, ∨(⊥, β), Ł4) == true
@test alphasat(MVHSTableau, α, ∨(⊥, ⊤), Ł4) == true
@test alphasat(MVHSTableau, α, ∨(α, ⊥), Ł4) == true
@test alphasat(MVHSTableau, α, ∨(α, α), Ł4) == true
@test alphasat(MVHSTableau, α, ∨(α, β), Ł4) == true
@test alphasat(MVHSTableau, α, ∨(α, ⊤), Ł4) == true
@test alphasat(MVHSTableau, α, ∨(β, ⊥), Ł4) == true
@test alphasat(MVHSTableau, α, ∨(β, α), Ł4) == true
@test alphasat(MVHSTableau, α, ∨(β, β), Ł4) == true
@test alphasat(MVHSTableau, α, ∨(β, ⊤), Ł4) == true
@test alphasat(MVHSTableau, α, ∨(⊤, ⊥), Ł4) == true
@test alphasat(MVHSTableau, α, ∨(⊤, α), Ł4) == true
@test alphasat(MVHSTableau, α, ∨(⊤, β), Ł4) == true
@test alphasat(MVHSTableau, α, ∨(⊤, ⊤), Ł4) == true

@test alphasat(MVHSTableau, β, ∨(⊥, ⊥), Ł4) == false
@test alphasat(MVHSTableau, β, ∨(⊥, α), Ł4) == false
@test alphasat(MVHSTableau, β, ∨(⊥, β), Ł4) == true
@test alphasat(MVHSTableau, β, ∨(⊥, ⊤), Ł4) == true
@test alphasat(MVHSTableau, β, ∨(α, ⊥), Ł4) == false
@test alphasat(MVHSTableau, β, ∨(α, α), Ł4) == false
@test alphasat(MVHSTableau, β, ∨(α, β), Ł4) == true
@test alphasat(MVHSTableau, β, ∨(α, ⊤), Ł4) == true
@test alphasat(MVHSTableau, β, ∨(β, ⊥), Ł4) == true
@test alphasat(MVHSTableau, β, ∨(β, α), Ł4) == true
@test alphasat(MVHSTableau, β, ∨(β, β), Ł4) == true
@test alphasat(MVHSTableau, β, ∨(β, ⊤), Ł4) == true
@test alphasat(MVHSTableau, β, ∨(⊤, ⊥), Ł4) == true
@test alphasat(MVHSTableau, β, ∨(⊤, α), Ł4) == true
@test alphasat(MVHSTableau, β, ∨(⊤, β), Ł4) == true
@test alphasat(MVHSTableau, β, ∨(⊤, ⊤), Ł4) == true

@test alphasat(MVHSTableau, ⊤, ∨(⊥, ⊥), Ł4) == false
@test alphasat(MVHSTableau, ⊤, ∨(⊥, α), Ł4) == false
@test alphasat(MVHSTableau, ⊤, ∨(⊥, β), Ł4) == false
@test alphasat(MVHSTableau, ⊤, ∨(⊥, ⊤), Ł4) == true
@test alphasat(MVHSTableau, ⊤, ∨(α, ⊥), Ł4) == false
@test alphasat(MVHSTableau, ⊤, ∨(α, α), Ł4) == false
@test alphasat(MVHSTableau, ⊤, ∨(α, β), Ł4) == false
@test alphasat(MVHSTableau, ⊤, ∨(α, ⊤), Ł4) == true
@test alphasat(MVHSTableau, ⊤, ∨(β, ⊥), Ł4) == false
@test alphasat(MVHSTableau, ⊤, ∨(β, α), Ł4) == false
@test alphasat(MVHSTableau, ⊤, ∨(β, β), Ł4) == false
@test alphasat(MVHSTableau, ⊤, ∨(β, ⊤), Ł4) == true
@test alphasat(MVHSTableau, ⊤, ∨(⊤, ⊥), Ł4) == true
@test alphasat(MVHSTableau, ⊤, ∨(⊤, α), Ł4) == true
@test alphasat(MVHSTableau, ⊤, ∨(⊤, β), Ł4) == true
@test alphasat(MVHSTableau, ⊤, ∨(⊤, ⊤), Ł4) == true

@test alphasat(MVHSTableau, ⊥, ∨(p, ⊥), Ł4) == true
@test alphasat(MVHSTableau, ⊥, ∨(p, α), Ł4) == true
@test alphasat(MVHSTableau, ⊥, ∨(p, β), Ł4) == true
@test alphasat(MVHSTableau, ⊥, ∨(p, ⊤), Ł4) == true
@test alphasat(MVHSTableau, α, ∨(p, ⊥), Ł4) == true
@test alphasat(MVHSTableau, α, ∨(p, α), Ł4) == true
@test alphasat(MVHSTableau, α, ∨(p, β), Ł4) == true
@test alphasat(MVHSTableau, α, ∨(p, ⊤), Ł4) == true
@test alphasat(MVHSTableau, β, ∨(p, ⊥), Ł4) == true
@test alphasat(MVHSTableau, β, ∨(p, α), Ł4) == true
@test alphasat(MVHSTableau, β, ∨(p, β), Ł4) == true
@test alphasat(MVHSTableau, β, ∨(p, ⊤), Ł4) == true
@test alphasat(MVHSTableau, ⊤, ∨(p, ⊥), Ł4) == true
@test alphasat(MVHSTableau, ⊤, ∨(p, α), Ł4) == true
@test alphasat(MVHSTableau, ⊤, ∨(p, β), Ł4) == true
@test alphasat(MVHSTableau, ⊤, ∨(p, ⊤), Ł4) == true

@test alphasat(MVHSTableau, ⊥, ∨(⊥, p), Ł4) == true
@test alphasat(MVHSTableau, ⊥, ∨(α, p), Ł4) == true
@test alphasat(MVHSTableau, ⊥, ∨(β, p), Ł4) == true
@test alphasat(MVHSTableau, ⊥, ∨(⊤, p), Ł4) == true
@test alphasat(MVHSTableau, α, ∨(⊥, p), Ł4) == true
@test alphasat(MVHSTableau, α, ∨(α, p), Ł4) == true
@test alphasat(MVHSTableau, α, ∨(β, p), Ł4) == true
@test alphasat(MVHSTableau, α, ∨(⊤, p), Ł4) == true
@test alphasat(MVHSTableau, β, ∨(⊥, p), Ł4) == true
@test alphasat(MVHSTableau, β, ∨(α, p), Ł4) == true
@test alphasat(MVHSTableau, β, ∨(β, p), Ł4) == true
@test alphasat(MVHSTableau, β, ∨(⊤, p), Ł4) == true
@test alphasat(MVHSTableau, ⊤, ∨(⊥, p), Ł4) == true
@test alphasat(MVHSTableau, ⊤, ∨(α, p), Ł4) == true
@test alphasat(MVHSTableau, ⊤, ∨(β, p), Ł4) == true
@test alphasat(MVHSTableau, ⊤, ∨(⊤, p), Ł4) == true

@test alphasat(MVHSTableau, ⊥, ∨(p, p), Ł4)
@test alphasat(MVHSTableau, α, ∨(p, p), Ł4)
@test alphasat(MVHSTableau, β, ∨(p, p), Ł4)
@test alphasat(MVHSTableau, ⊤, ∨(p, p), Ł4)

@test alphasat(MVHSTableau, ⊥, ∨(p, q), Ł4)
@test alphasat(MVHSTableau, α, ∨(p, q), Ł4)
@test alphasat(MVHSTableau, β, ∨(p, q), Ł4)
@test alphasat(MVHSTableau, ⊤, ∨(p, q), Ł4)

@test alphasat(MVHSTableau, ⊥, ∨(q, q), Ł4)
@test alphasat(MVHSTableau, α, ∨(q, q), Ł4)
@test alphasat(MVHSTableau, β, ∨(q, q), Ł4)
@test alphasat(MVHSTableau, ⊤, ∨(q, q), Ł4)

################################################################################
## (Strong) conjunction ########################################################
################################################################################

@test alphasat(MVHSTableau, ⊥, ∧(⊥, ⊥), Ł4) == true
@test alphasat(MVHSTableau, ⊥, ∧(⊥, α), Ł4) == true
@test alphasat(MVHSTableau, ⊥, ∧(⊥, β), Ł4) == true
@test alphasat(MVHSTableau, ⊥, ∧(⊥, ⊤), Ł4) == true
@test alphasat(MVHSTableau, ⊥, ∧(α, ⊥), Ł4) == true
@test alphasat(MVHSTableau, ⊥, ∧(α, α), Ł4) == true
@test alphasat(MVHSTableau, ⊥, ∧(α, β), Ł4) == true
@test alphasat(MVHSTableau, ⊥, ∧(α, ⊤), Ł4) == true
@test alphasat(MVHSTableau, ⊥, ∧(β, ⊥), Ł4) == true
@test alphasat(MVHSTableau, ⊥, ∧(β, α), Ł4) == true
@test alphasat(MVHSTableau, ⊥, ∧(β, β), Ł4) == true
@test alphasat(MVHSTableau, ⊥, ∧(β, ⊤), Ł4) == true
@test alphasat(MVHSTableau, ⊥, ∧(⊤, ⊥), Ł4) == true
@test alphasat(MVHSTableau, ⊥, ∧(⊤, α), Ł4) == true
@test alphasat(MVHSTableau, ⊥, ∧(⊤, β), Ł4) == true
@test alphasat(MVHSTableau, ⊥, ∧(⊤, ⊤), Ł4) == true

@test alphasat(MVHSTableau, α, ∧(⊥, ⊥), Ł4) == false
@test alphasat(MVHSTableau, α, ∧(⊥, α), Ł4) == false
@test alphasat(MVHSTableau, α, ∧(⊥, β), Ł4) == false
@test alphasat(MVHSTableau, α, ∧(⊥, ⊤), Ł4) == false
@test alphasat(MVHSTableau, α, ∧(α, ⊥), Ł4) == false
@test alphasat(MVHSTableau, α, ∧(α, α), Ł4) == false
@test alphasat(MVHSTableau, α, ∧(α, β), Ł4) == false
@test alphasat(MVHSTableau, α, ∧(α, ⊤), Ł4) == true
@test alphasat(MVHSTableau, α, ∧(β, ⊥), Ł4) == false
@test alphasat(MVHSTableau, α, ∧(β, α), Ł4) == false
@test alphasat(MVHSTableau, α, ∧(β, β), Ł4) == true
@test alphasat(MVHSTableau, α, ∧(β, ⊤), Ł4) == true
@test alphasat(MVHSTableau, α, ∧(⊤, ⊥), Ł4) == false
@test alphasat(MVHSTableau, α, ∧(⊤, α), Ł4) == true
@test alphasat(MVHSTableau, α, ∧(⊤, β), Ł4) == true
@test alphasat(MVHSTableau, α, ∧(⊤, ⊤), Ł4) == true

@test alphasat(MVHSTableau, β, ∧(⊥, ⊥), Ł4) == false
@test alphasat(MVHSTableau, β, ∧(⊥, α), Ł4) == false
@test alphasat(MVHSTableau, β, ∧(⊥, β), Ł4) == false
@test alphasat(MVHSTableau, β, ∧(⊥, ⊤), Ł4) == false
@test alphasat(MVHSTableau, β, ∧(α, ⊥), Ł4) == false
@test alphasat(MVHSTableau, β, ∧(α, α), Ł4) == false
@test alphasat(MVHSTableau, β, ∧(α, β), Ł4) == false
@test alphasat(MVHSTableau, β, ∧(α, ⊤), Ł4) == false
@test alphasat(MVHSTableau, β, ∧(β, ⊥), Ł4) == false
@test alphasat(MVHSTableau, β, ∧(β, α), Ł4) == false
@test alphasat(MVHSTableau, β, ∧(β, β), Ł4) == false
@test alphasat(MVHSTableau, β, ∧(β, ⊤), Ł4) == true
@test alphasat(MVHSTableau, β, ∧(⊤, ⊥), Ł4) == false
@test alphasat(MVHSTableau, β, ∧(⊤, α), Ł4) == false
@test alphasat(MVHSTableau, β, ∧(⊤, β), Ł4) == true
@test alphasat(MVHSTableau, β, ∧(⊤, ⊤), Ł4) == true

@test alphasat(MVHSTableau, ⊤, ∧(⊥, ⊥), Ł4) == false
@test alphasat(MVHSTableau, ⊤, ∧(⊥, α), Ł4) == false
@test alphasat(MVHSTableau, ⊤, ∧(⊥, β), Ł4) == false
@test alphasat(MVHSTableau, ⊤, ∧(⊥, ⊤), Ł4) == false
@test alphasat(MVHSTableau, ⊤, ∧(α, ⊥), Ł4) == false
@test alphasat(MVHSTableau, ⊤, ∧(α, α), Ł4) == false
@test alphasat(MVHSTableau, ⊤, ∧(α, β), Ł4) == false
@test alphasat(MVHSTableau, ⊤, ∧(α, ⊤), Ł4) == false
@test alphasat(MVHSTableau, ⊤, ∧(β, ⊥), Ł4) == false
@test alphasat(MVHSTableau, ⊤, ∧(β, α), Ł4) == false
@test alphasat(MVHSTableau, ⊤, ∧(β, β), Ł4) == false
@test alphasat(MVHSTableau, ⊤, ∧(β, ⊤), Ł4) == false
@test alphasat(MVHSTableau, ⊤, ∧(⊤, ⊥), Ł4) == false
@test alphasat(MVHSTableau, ⊤, ∧(⊤, α), Ł4) == false
@test alphasat(MVHSTableau, ⊤, ∧(⊤, β), Ł4) == false
@test alphasat(MVHSTableau, ⊤, ∧(⊤, ⊤), Ł4) == true

@test alphasat(MVHSTableau, ⊥, ∧(p, ⊥), Ł4) == true
@test alphasat(MVHSTableau, ⊥, ∧(p, α), Ł4) == true
@test alphasat(MVHSTableau, ⊥, ∧(p, β), Ł4) == true
@test alphasat(MVHSTableau, ⊥, ∧(p, ⊤), Ł4) == true
@test alphasat(MVHSTableau, α, ∧(p, ⊥), Ł4) == false
@test alphasat(MVHSTableau, α, ∧(p, α), Ł4) == true
@test alphasat(MVHSTableau, α, ∧(p, β), Ł4) == true
@test alphasat(MVHSTableau, α, ∧(p, ⊤), Ł4) == true
@test alphasat(MVHSTableau, β, ∧(p, ⊥), Ł4) == false
@test alphasat(MVHSTableau, β, ∧(p, α), Ł4) == false
@test alphasat(MVHSTableau, β, ∧(p, β), Ł4) == true
@test alphasat(MVHSTableau, β, ∧(p, ⊤), Ł4) == true
@test alphasat(MVHSTableau, ⊤, ∧(p, ⊥), Ł4) == false
@test alphasat(MVHSTableau, ⊤, ∧(p, α), Ł4) == false
@test alphasat(MVHSTableau, ⊤, ∧(p, β), Ł4) == false
@test alphasat(MVHSTableau, ⊤, ∧(p, ⊤), Ł4) == true

@test alphasat(MVHSTableau, ⊥, ∧(⊥, p), Ł4) == true
@test alphasat(MVHSTableau, ⊥, ∧(α, p), Ł4) == true
@test alphasat(MVHSTableau, ⊥, ∧(β, p), Ł4) == true
@test alphasat(MVHSTableau, ⊥, ∧(⊤, p), Ł4) == true
@test alphasat(MVHSTableau, α, ∧(⊥, p), Ł4) == false
@test alphasat(MVHSTableau, α, ∧(α, p), Ł4) == true
@test alphasat(MVHSTableau, α, ∧(β, p), Ł4) == true
@test alphasat(MVHSTableau, α, ∧(⊤, p), Ł4) == true
@test alphasat(MVHSTableau, β, ∧(⊥, p), Ł4) == false
@test alphasat(MVHSTableau, β, ∧(α, p), Ł4) == false
@test alphasat(MVHSTableau, β, ∧(β, p), Ł4) == true
@test alphasat(MVHSTableau, β, ∧(⊤, p), Ł4) == true
@test alphasat(MVHSTableau, ⊤, ∧(⊥, p), Ł4) == false
@test alphasat(MVHSTableau, ⊤, ∧(α, p), Ł4) == false
@test alphasat(MVHSTableau, ⊤, ∧(β, p), Ł4) == false
@test alphasat(MVHSTableau, ⊤, ∧(⊤, p), Ł4) == true

@test alphasat(MVHSTableau, ⊥, ∧(p, p), Ł4)
@test alphasat(MVHSTableau, α, ∧(p, p), Ł4)
@test alphasat(MVHSTableau, β, ∧(p, p), Ł4)
@test alphasat(MVHSTableau, ⊤, ∧(p, p), Ł4)

@test alphasat(MVHSTableau, ⊥, ∧(p, q), Ł4)
@test alphasat(MVHSTableau, α, ∧(p, q), Ł4)
@test alphasat(MVHSTableau, β, ∧(p, q), Ł4)
@test alphasat(MVHSTableau, ⊤, ∧(p, q), Ł4)

@test alphasat(MVHSTableau, ⊥, ∧(q, p), Ł4)
@test alphasat(MVHSTableau, α, ∧(q, p), Ł4)
@test alphasat(MVHSTableau, β, ∧(q, p), Ł4)
@test alphasat(MVHSTableau, ⊤, ∧(q, p), Ł4)

################################################################################
## Implication #################################################################
################################################################################

@test alphasat(MVHSTableau, ⊥, →(⊥, ⊥), Ł4) == true
@test alphasat(MVHSTableau, ⊥, →(⊥, α), Ł4) == true
@test alphasat(MVHSTableau, ⊥, →(⊥, β), Ł4) == true
@test alphasat(MVHSTableau, ⊥, →(⊥, ⊤), Ł4) == true
@test alphasat(MVHSTableau, ⊥, →(α, ⊥), Ł4) == true
@test alphasat(MVHSTableau, ⊥, →(α, α), Ł4) == true
@test alphasat(MVHSTableau, ⊥, →(α, β), Ł4) == true
@test alphasat(MVHSTableau, ⊥, →(α, ⊤), Ł4) == true
@test alphasat(MVHSTableau, ⊥, →(β, ⊥), Ł4) == true
@test alphasat(MVHSTableau, ⊥, →(β, α), Ł4) == true
@test alphasat(MVHSTableau, ⊥, →(β, β), Ł4) == true
@test alphasat(MVHSTableau, ⊥, →(β, ⊤), Ł4) == true
@test alphasat(MVHSTableau, ⊥, →(⊤, ⊥), Ł4) == true
@test alphasat(MVHSTableau, ⊥, →(⊤, α), Ł4) == true
@test alphasat(MVHSTableau, ⊥, →(⊤, β), Ł4) == true
@test alphasat(MVHSTableau, ⊥, →(⊤, ⊤), Ł4) == true

@test alphasat(MVHSTableau, α, →(⊥, ⊥), Ł4) == true
@test alphasat(MVHSTableau, α, →(⊥, α), Ł4) == true
@test alphasat(MVHSTableau, α, →(⊥, β), Ł4) == true
@test alphasat(MVHSTableau, α, →(⊥, ⊤), Ł4) == true
@test alphasat(MVHSTableau, α, →(α, ⊥), Ł4) == true
@test alphasat(MVHSTableau, α, →(α, α), Ł4) == true
@test alphasat(MVHSTableau, α, →(α, β), Ł4) == true
@test alphasat(MVHSTableau, α, →(α, ⊤), Ł4) == true
@test alphasat(MVHSTableau, α, →(β, ⊥), Ł4) == true
@test alphasat(MVHSTableau, α, →(β, α), Ł4) == true
@test alphasat(MVHSTableau, α, →(β, β), Ł4) == true
@test alphasat(MVHSTableau, α, →(β, ⊤), Ł4) == true
@test alphasat(MVHSTableau, α, →(⊤, ⊥), Ł4) == false
@test alphasat(MVHSTableau, α, →(⊤, α), Ł4) == true
@test alphasat(MVHSTableau, α, →(⊤, β), Ł4) == true
@test alphasat(MVHSTableau, α, →(⊤, ⊤), Ł4) == true

@test alphasat(MVHSTableau, β, →(⊥, ⊥), Ł4) == true
@test alphasat(MVHSTableau, β, →(⊥, α), Ł4) == true
@test alphasat(MVHSTableau, β, →(⊥, β), Ł4) == true
@test alphasat(MVHSTableau, β, →(⊥, ⊤), Ł4) == true
@test alphasat(MVHSTableau, β, →(α, ⊥), Ł4) == true
@test alphasat(MVHSTableau, β, →(α, α), Ł4) == true
@test alphasat(MVHSTableau, β, →(α, β), Ł4) == true
@test alphasat(MVHSTableau, β, →(α, ⊤), Ł4) == true
@test alphasat(MVHSTableau, β, →(β, ⊥), Ł4) == false
@test alphasat(MVHSTableau, β, →(β, α), Ł4) == true
@test alphasat(MVHSTableau, β, →(β, β), Ł4) == true
@test alphasat(MVHSTableau, β, →(β, ⊤), Ł4) == true
@test alphasat(MVHSTableau, β, →(⊤, ⊥), Ł4) == false
@test alphasat(MVHSTableau, β, →(⊤, α), Ł4) == false
@test alphasat(MVHSTableau, β, →(⊤, β), Ł4) == true
@test alphasat(MVHSTableau, β, →(⊤, ⊤), Ł4) == true

@test alphasat(MVHSTableau, ⊤, →(⊥, ⊥), Ł4) == true
@test alphasat(MVHSTableau, ⊤, →(⊥, α), Ł4) == true
@test alphasat(MVHSTableau, ⊤, →(⊥, β), Ł4) == true
@test alphasat(MVHSTableau, ⊤, →(⊥, ⊤), Ł4) == true
@test alphasat(MVHSTableau, ⊤, →(α, ⊥), Ł4) == false
@test alphasat(MVHSTableau, ⊤, →(α, α), Ł4) == true
@test alphasat(MVHSTableau, ⊤, →(α, β), Ł4) == true
@test alphasat(MVHSTableau, ⊤, →(α, ⊤), Ł4) == true
@test alphasat(MVHSTableau, ⊤, →(β, ⊥), Ł4) == false
@test alphasat(MVHSTableau, ⊤, →(β, α), Ł4) == false
@test alphasat(MVHSTableau, ⊤, →(β, β), Ł4) == true
@test alphasat(MVHSTableau, ⊤, →(β, ⊤), Ł4) == true
@test alphasat(MVHSTableau, ⊤, →(⊤, ⊥), Ł4) == false
@test alphasat(MVHSTableau, ⊤, →(⊤, α), Ł4) == false
@test alphasat(MVHSTableau, ⊤, →(⊤, β), Ł4) == false
@test alphasat(MVHSTableau, ⊤, →(⊤, ⊤), Ł4) == true

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
)), Ł4, timeout=timeout)

if !isnothing(result)
    @test result == false
end
