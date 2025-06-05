################################################################################
#### H4 ########################################################################
################################################################################

using SoleLogics.ManyValuedLogics: H4
using SoleLogics.ManyValuedLogics: α, β

p, q = Atom.(["p", "q"])

timeout = 60

################################################################################
## Base cases ##################################################################
################################################################################

@test alphasat(MVLTLFPTableau, ⊥, ⊥, H4) == true
@test alphasat(MVLTLFPTableau, ⊥, α, H4) == true
@test alphasat(MVLTLFPTableau, ⊥, β, H4) == true
@test alphasat(MVLTLFPTableau, ⊥, ⊤, H4) == true
@test alphasat(MVLTLFPTableau, α, ⊥, H4) == false
@test alphasat(MVLTLFPTableau, α, α, H4) == true
@test alphasat(MVLTLFPTableau, α, β, H4) == false
@test alphasat(MVLTLFPTableau, α, ⊤, H4) == true
@test alphasat(MVLTLFPTableau, β, ⊥, H4) == false
@test alphasat(MVLTLFPTableau, β, α, H4) == false
@test alphasat(MVLTLFPTableau, β, β, H4) == true
@test alphasat(MVLTLFPTableau, β, ⊤, H4) == true
@test alphasat(MVLTLFPTableau, ⊤, ⊥, H4) == false
@test alphasat(MVLTLFPTableau, ⊤, α, H4) == false
@test alphasat(MVLTLFPTableau, ⊤, β, H4) == false
@test alphasat(MVLTLFPTableau, ⊤, ⊤, H4) == true

@test alphasat(MVLTLFPTableau, ⊥, p, H4) == true
@test alphasat(MVLTLFPTableau, α, p, H4) == true
@test alphasat(MVLTLFPTableau, β, p, H4) == true
@test alphasat(MVLTLFPTableau, ⊤, p, H4) == true

################################################################################
## (Strong) disjuction #########################################################
################################################################################

@test alphasat(MVLTLFPTableau, ⊥, ∨(⊥, ⊥), H4) == true
@test alphasat(MVLTLFPTableau, ⊥, ∨(⊥, α), H4) == true
@test alphasat(MVLTLFPTableau, ⊥, ∨(⊥, β), H4) == true
@test alphasat(MVLTLFPTableau, ⊥, ∨(⊥, ⊤), H4) == true
@test alphasat(MVLTLFPTableau, ⊥, ∨(α, ⊥), H4) == true
@test alphasat(MVLTLFPTableau, ⊥, ∨(α, α), H4) == true
@test alphasat(MVLTLFPTableau, ⊥, ∨(α, β), H4) == true
@test alphasat(MVLTLFPTableau, ⊥, ∨(α, ⊤), H4) == true
@test alphasat(MVLTLFPTableau, ⊥, ∨(β, ⊥), H4) == true
@test alphasat(MVLTLFPTableau, ⊥, ∨(β, α), H4) == true
@test alphasat(MVLTLFPTableau, ⊥, ∨(β, β), H4) == true
@test alphasat(MVLTLFPTableau, ⊥, ∨(β, ⊤), H4) == true
@test alphasat(MVLTLFPTableau, ⊥, ∨(⊤, ⊥), H4) == true
@test alphasat(MVLTLFPTableau, ⊥, ∨(⊤, α), H4) == true
@test alphasat(MVLTLFPTableau, ⊥, ∨(⊤, β), H4) == true
@test alphasat(MVLTLFPTableau, ⊥, ∨(⊤, ⊤), H4) == true

@test alphasat(MVLTLFPTableau, α, ∨(⊥, ⊥), H4) == false
@test alphasat(MVLTLFPTableau, α, ∨(⊥, α), H4) == true
@test alphasat(MVLTLFPTableau, α, ∨(⊥, β), H4) == false
@test alphasat(MVLTLFPTableau, α, ∨(⊥, ⊤), H4) == true
@test alphasat(MVLTLFPTableau, α, ∨(α, ⊥), H4) == true
@test alphasat(MVLTLFPTableau, α, ∨(α, α), H4) == true
@test alphasat(MVLTLFPTableau, α, ∨(α, β), H4) == true
@test alphasat(MVLTLFPTableau, α, ∨(α, ⊤), H4) == true
@test alphasat(MVLTLFPTableau, α, ∨(β, ⊥), H4) == false
@test alphasat(MVLTLFPTableau, α, ∨(β, α), H4) == true
@test alphasat(MVLTLFPTableau, α, ∨(β, β), H4) == false
@test alphasat(MVLTLFPTableau, α, ∨(β, ⊤), H4) == true
@test alphasat(MVLTLFPTableau, α, ∨(⊤, ⊥), H4) == true
@test alphasat(MVLTLFPTableau, α, ∨(⊤, α), H4) == true
@test alphasat(MVLTLFPTableau, α, ∨(⊤, β), H4) == true
@test alphasat(MVLTLFPTableau, α, ∨(⊤, ⊤), H4) == true

@test alphasat(MVLTLFPTableau, β, ∨(⊥, ⊥), H4) == false
@test alphasat(MVLTLFPTableau, β, ∨(⊥, α), H4) == false
@test alphasat(MVLTLFPTableau, β, ∨(⊥, β), H4) == true
@test alphasat(MVLTLFPTableau, β, ∨(⊥, ⊤), H4) == true
@test alphasat(MVLTLFPTableau, β, ∨(α, ⊥), H4) == false
@test alphasat(MVLTLFPTableau, β, ∨(α, α), H4) == false
@test alphasat(MVLTLFPTableau, β, ∨(α, β), H4) == true
@test alphasat(MVLTLFPTableau, β, ∨(α, ⊤), H4) == true
@test alphasat(MVLTLFPTableau, β, ∨(β, ⊥), H4) == true
@test alphasat(MVLTLFPTableau, β, ∨(β, α), H4) == true
@test alphasat(MVLTLFPTableau, β, ∨(β, β), H4) == true
@test alphasat(MVLTLFPTableau, β, ∨(β, ⊤), H4) == true
@test alphasat(MVLTLFPTableau, β, ∨(⊤, ⊥), H4) == true
@test alphasat(MVLTLFPTableau, β, ∨(⊤, α), H4) == true
@test alphasat(MVLTLFPTableau, β, ∨(⊤, β), H4) == true
@test alphasat(MVLTLFPTableau, β, ∨(⊤, ⊤), H4) == true

@test alphasat(MVLTLFPTableau, ⊤, ∨(⊥, ⊥), H4) == false
@test alphasat(MVLTLFPTableau, ⊤, ∨(⊥, α), H4) == false
@test alphasat(MVLTLFPTableau, ⊤, ∨(⊥, β), H4) == false
@test alphasat(MVLTLFPTableau, ⊤, ∨(⊥, ⊤), H4) == true
@test alphasat(MVLTLFPTableau, ⊤, ∨(α, ⊥), H4) == false
@test alphasat(MVLTLFPTableau, ⊤, ∨(α, α), H4) == false
@test alphasat(MVLTLFPTableau, ⊤, ∨(α, β), H4) == true
@test alphasat(MVLTLFPTableau, ⊤, ∨(α, ⊤), H4) == true
@test alphasat(MVLTLFPTableau, ⊤, ∨(β, ⊥), H4) == false
@test alphasat(MVLTLFPTableau, ⊤, ∨(β, α), H4) == true
@test alphasat(MVLTLFPTableau, ⊤, ∨(β, β), H4) == false
@test alphasat(MVLTLFPTableau, ⊤, ∨(β, ⊤), H4) == true
@test alphasat(MVLTLFPTableau, ⊤, ∨(⊤, ⊥), H4) == true
@test alphasat(MVLTLFPTableau, ⊤, ∨(⊤, α), H4) == true
@test alphasat(MVLTLFPTableau, ⊤, ∨(⊤, β), H4) == true
@test alphasat(MVLTLFPTableau, ⊤, ∨(⊤, ⊤), H4) == true

@test alphasat(MVLTLFPTableau, ⊥, ∨(p, ⊥), H4) == true
@test alphasat(MVLTLFPTableau, ⊥, ∨(p, α), H4) == true
@test alphasat(MVLTLFPTableau, ⊥, ∨(p, β), H4) == true
@test alphasat(MVLTLFPTableau, ⊥, ∨(p, ⊤), H4) == true
@test alphasat(MVLTLFPTableau, α, ∨(p, ⊥), H4) == true
@test alphasat(MVLTLFPTableau, α, ∨(p, α), H4) == true
@test alphasat(MVLTLFPTableau, α, ∨(p, β), H4) == true
@test alphasat(MVLTLFPTableau, α, ∨(p, ⊤), H4) == true
@test alphasat(MVLTLFPTableau, β, ∨(p, ⊥), H4) == true
@test alphasat(MVLTLFPTableau, β, ∨(p, α), H4) == true
@test alphasat(MVLTLFPTableau, β, ∨(p, β), H4) == true
@test alphasat(MVLTLFPTableau, β, ∨(p, ⊤), H4) == true
@test alphasat(MVLTLFPTableau, ⊤, ∨(p, ⊥), H4) == true
@test alphasat(MVLTLFPTableau, ⊤, ∨(p, α), H4) == true
@test alphasat(MVLTLFPTableau, ⊤, ∨(p, β), H4) == true
@test alphasat(MVLTLFPTableau, ⊤, ∨(p, ⊤), H4) == true

@test alphasat(MVLTLFPTableau, ⊥, ∨(⊥, p), H4) == true
@test alphasat(MVLTLFPTableau, ⊥, ∨(α, p), H4) == true
@test alphasat(MVLTLFPTableau, ⊥, ∨(β, p), H4) == true
@test alphasat(MVLTLFPTableau, ⊥, ∨(⊤, p), H4) == true
@test alphasat(MVLTLFPTableau, α, ∨(⊥, p), H4) == true
@test alphasat(MVLTLFPTableau, α, ∨(α, p), H4) == true
@test alphasat(MVLTLFPTableau, α, ∨(β, p), H4) == true
@test alphasat(MVLTLFPTableau, α, ∨(⊤, p), H4) == true
@test alphasat(MVLTLFPTableau, β, ∨(⊥, p), H4) == true
@test alphasat(MVLTLFPTableau, β, ∨(α, p), H4) == true
@test alphasat(MVLTLFPTableau, β, ∨(β, p), H4) == true
@test alphasat(MVLTLFPTableau, β, ∨(⊤, p), H4) == true
@test alphasat(MVLTLFPTableau, ⊤, ∨(⊥, p), H4) == true
@test alphasat(MVLTLFPTableau, ⊤, ∨(α, p), H4) == true
@test alphasat(MVLTLFPTableau, ⊤, ∨(β, p), H4) == true
@test alphasat(MVLTLFPTableau, ⊤, ∨(⊤, p), H4) == true

@test alphasat(MVLTLFPTableau, ⊥, ∨(p, p), H4)
@test alphasat(MVLTLFPTableau, α, ∨(p, p), H4)
@test alphasat(MVLTLFPTableau, β, ∨(p, p), H4)
@test alphasat(MVLTLFPTableau, ⊤, ∨(p, p), H4)

@test alphasat(MVLTLFPTableau, ⊥, ∨(p, q), H4)
@test alphasat(MVLTLFPTableau, α, ∨(p, q), H4)
@test alphasat(MVLTLFPTableau, β, ∨(p, q), H4)
@test alphasat(MVLTLFPTableau, ⊤, ∨(p, q), H4)

@test alphasat(MVLTLFPTableau, ⊥, ∨(q, q), H4)
@test alphasat(MVLTLFPTableau, α, ∨(q, q), H4)
@test alphasat(MVLTLFPTableau, β, ∨(q, q), H4)
@test alphasat(MVLTLFPTableau, ⊤, ∨(q, q), H4)

################################################################################
## (Strong) conjunction ########################################################
################################################################################

@test alphasat(MVLTLFPTableau, ⊥, ∧(⊥, ⊥), H4) == true
@test alphasat(MVLTLFPTableau, ⊥, ∧(⊥, α), H4) == true
@test alphasat(MVLTLFPTableau, ⊥, ∧(⊥, β), H4) == true
@test alphasat(MVLTLFPTableau, ⊥, ∧(⊥, ⊤), H4) == true
@test alphasat(MVLTLFPTableau, ⊥, ∧(α, ⊥), H4) == true
@test alphasat(MVLTLFPTableau, ⊥, ∧(α, α), H4) == true
@test alphasat(MVLTLFPTableau, ⊥, ∧(α, β), H4) == true
@test alphasat(MVLTLFPTableau, ⊥, ∧(α, ⊤), H4) == true
@test alphasat(MVLTLFPTableau, ⊥, ∧(β, ⊥), H4) == true
@test alphasat(MVLTLFPTableau, ⊥, ∧(β, α), H4) == true
@test alphasat(MVLTLFPTableau, ⊥, ∧(β, β), H4) == true
@test alphasat(MVLTLFPTableau, ⊥, ∧(β, ⊤), H4) == true
@test alphasat(MVLTLFPTableau, ⊥, ∧(⊤, ⊥), H4) == true
@test alphasat(MVLTLFPTableau, ⊥, ∧(⊤, α), H4) == true
@test alphasat(MVLTLFPTableau, ⊥, ∧(⊤, β), H4) == true
@test alphasat(MVLTLFPTableau, ⊥, ∧(⊤, ⊤), H4) == true

@test alphasat(MVLTLFPTableau, α, ∧(⊥, ⊥), H4) == false
@test alphasat(MVLTLFPTableau, α, ∧(⊥, α), H4) == false
@test alphasat(MVLTLFPTableau, α, ∧(⊥, β), H4) == false
@test alphasat(MVLTLFPTableau, α, ∧(⊥, ⊤), H4) == false
@test alphasat(MVLTLFPTableau, α, ∧(α, ⊥), H4) == false
@test alphasat(MVLTLFPTableau, α, ∧(α, α), H4) == true
@test alphasat(MVLTLFPTableau, α, ∧(α, β), H4) == false
@test alphasat(MVLTLFPTableau, α, ∧(α, ⊤), H4) == true
@test alphasat(MVLTLFPTableau, α, ∧(β, ⊥), H4) == false
@test alphasat(MVLTLFPTableau, α, ∧(β, α), H4) == false
@test alphasat(MVLTLFPTableau, α, ∧(β, β), H4) == false
@test alphasat(MVLTLFPTableau, α, ∧(β, ⊤), H4) == false
@test alphasat(MVLTLFPTableau, α, ∧(⊤, ⊥), H4) == false
@test alphasat(MVLTLFPTableau, α, ∧(⊤, α), H4) == true
@test alphasat(MVLTLFPTableau, α, ∧(⊤, β), H4) == false
@test alphasat(MVLTLFPTableau, α, ∧(⊤, ⊤), H4) == true

@test alphasat(MVLTLFPTableau, β, ∧(⊥, ⊥), H4) == false
@test alphasat(MVLTLFPTableau, β, ∧(⊥, α), H4) == false
@test alphasat(MVLTLFPTableau, β, ∧(⊥, β), H4) == false
@test alphasat(MVLTLFPTableau, β, ∧(⊥, ⊤), H4) == false
@test alphasat(MVLTLFPTableau, β, ∧(α, ⊥), H4) == false
@test alphasat(MVLTLFPTableau, β, ∧(α, α), H4) == false
@test alphasat(MVLTLFPTableau, β, ∧(α, β), H4) == false
@test alphasat(MVLTLFPTableau, β, ∧(α, ⊤), H4) == false
@test alphasat(MVLTLFPTableau, β, ∧(β, ⊥), H4) == false
@test alphasat(MVLTLFPTableau, β, ∧(β, α), H4) == false
@test alphasat(MVLTLFPTableau, β, ∧(β, β), H4) == true
@test alphasat(MVLTLFPTableau, β, ∧(β, ⊤), H4) == true
@test alphasat(MVLTLFPTableau, β, ∧(⊤, ⊥), H4) == false
@test alphasat(MVLTLFPTableau, β, ∧(⊤, α), H4) == false
@test alphasat(MVLTLFPTableau, β, ∧(⊤, β), H4) == true
@test alphasat(MVLTLFPTableau, β, ∧(⊤, ⊤), H4) == true

@test alphasat(MVLTLFPTableau, ⊤, ∧(⊥, ⊥), H4) == false
@test alphasat(MVLTLFPTableau, ⊤, ∧(⊥, α), H4) == false
@test alphasat(MVLTLFPTableau, ⊤, ∧(⊥, β), H4) == false
@test alphasat(MVLTLFPTableau, ⊤, ∧(⊥, ⊤), H4) == false
@test alphasat(MVLTLFPTableau, ⊤, ∧(α, ⊥), H4) == false
@test alphasat(MVLTLFPTableau, ⊤, ∧(α, α), H4) == false
@test alphasat(MVLTLFPTableau, ⊤, ∧(α, β), H4) == false
@test alphasat(MVLTLFPTableau, ⊤, ∧(α, ⊤), H4) == false
@test alphasat(MVLTLFPTableau, ⊤, ∧(β, ⊥), H4) == false
@test alphasat(MVLTLFPTableau, ⊤, ∧(β, α), H4) == false
@test alphasat(MVLTLFPTableau, ⊤, ∧(β, β), H4) == false
@test alphasat(MVLTLFPTableau, ⊤, ∧(β, ⊤), H4) == false
@test alphasat(MVLTLFPTableau, ⊤, ∧(⊤, ⊥), H4) == false
@test alphasat(MVLTLFPTableau, ⊤, ∧(⊤, α), H4) == false
@test alphasat(MVLTLFPTableau, ⊤, ∧(⊤, β), H4) == false
@test alphasat(MVLTLFPTableau, ⊤, ∧(⊤, ⊤), H4) == true

@test alphasat(MVLTLFPTableau, ⊥, ∧(p, ⊥), H4) == true
@test alphasat(MVLTLFPTableau, ⊥, ∧(p, α), H4) == true
@test alphasat(MVLTLFPTableau, ⊥, ∧(p, β), H4) == true
@test alphasat(MVLTLFPTableau, ⊥, ∧(p, ⊤), H4) == true
@test alphasat(MVLTLFPTableau, α, ∧(p, ⊥), H4) == false
@test alphasat(MVLTLFPTableau, α, ∧(p, α), H4) == true
@test alphasat(MVLTLFPTableau, α, ∧(p, β), H4) == false
@test alphasat(MVLTLFPTableau, α, ∧(p, ⊤), H4) == true
@test alphasat(MVLTLFPTableau, β, ∧(p, ⊥), H4) == false
@test alphasat(MVLTLFPTableau, β, ∧(p, α), H4) == false
@test alphasat(MVLTLFPTableau, β, ∧(p, β), H4) == true
@test alphasat(MVLTLFPTableau, β, ∧(p, ⊤), H4) == true
@test alphasat(MVLTLFPTableau, ⊤, ∧(p, ⊥), H4) == false
@test alphasat(MVLTLFPTableau, ⊤, ∧(p, α), H4) == false
@test alphasat(MVLTLFPTableau, ⊤, ∧(p, β), H4) == false
@test alphasat(MVLTLFPTableau, ⊤, ∧(p, ⊤), H4) == true

@test alphasat(MVLTLFPTableau, ⊥, ∧(⊥, p), H4) == true
@test alphasat(MVLTLFPTableau, ⊥, ∧(α, p), H4) == true
@test alphasat(MVLTLFPTableau, ⊥, ∧(β, p), H4) == true
@test alphasat(MVLTLFPTableau, ⊥, ∧(⊤, p), H4) == true
@test alphasat(MVLTLFPTableau, α, ∧(⊥, p), H4) == false
@test alphasat(MVLTLFPTableau, α, ∧(α, p), H4) == true
@test alphasat(MVLTLFPTableau, α, ∧(β, p), H4) == false
@test alphasat(MVLTLFPTableau, α, ∧(⊤, p), H4) == true
@test alphasat(MVLTLFPTableau, β, ∧(⊥, p), H4) == false
@test alphasat(MVLTLFPTableau, β, ∧(α, p), H4) == false
@test alphasat(MVLTLFPTableau, β, ∧(β, p), H4) == true
@test alphasat(MVLTLFPTableau, β, ∧(⊤, p), H4) == true
@test alphasat(MVLTLFPTableau, ⊤, ∧(⊥, p), H4) == false
@test alphasat(MVLTLFPTableau, ⊤, ∧(α, p), H4) == false
@test alphasat(MVLTLFPTableau, ⊤, ∧(β, p), H4) == false
@test alphasat(MVLTLFPTableau, ⊤, ∧(⊤, p), H4) == true

@test alphasat(MVLTLFPTableau, ⊥, ∧(p, p), H4)
@test alphasat(MVLTLFPTableau, α, ∧(p, p), H4)
@test alphasat(MVLTLFPTableau, β, ∧(p, p), H4)
@test alphasat(MVLTLFPTableau, ⊤, ∧(p, p), H4)

@test alphasat(MVLTLFPTableau, ⊥, ∧(p, q), H4)
@test alphasat(MVLTLFPTableau, α, ∧(p, q), H4)
@test alphasat(MVLTLFPTableau, β, ∧(p, q), H4)
@test alphasat(MVLTLFPTableau, ⊤, ∧(p, q), H4)

@test alphasat(MVLTLFPTableau, ⊥, ∧(q, p), H4)
@test alphasat(MVLTLFPTableau, α, ∧(q, p), H4)
@test alphasat(MVLTLFPTableau, β, ∧(q, p), H4)
@test alphasat(MVLTLFPTableau, ⊤, ∧(q, p), H4)

################################################################################
## Implication #################################################################
################################################################################

@test alphasat(MVLTLFPTableau, ⊥, →(⊥, ⊥), H4) == true
@test alphasat(MVLTLFPTableau, ⊥, →(⊥, α), H4) == true
@test alphasat(MVLTLFPTableau, ⊥, →(⊥, β), H4) == true
@test alphasat(MVLTLFPTableau, ⊥, →(⊥, ⊤), H4) == true
@test alphasat(MVLTLFPTableau, ⊥, →(α, ⊥), H4) == true
@test alphasat(MVLTLFPTableau, ⊥, →(α, α), H4) == true
@test alphasat(MVLTLFPTableau, ⊥, →(α, β), H4) == true
@test alphasat(MVLTLFPTableau, ⊥, →(α, ⊤), H4) == true
@test alphasat(MVLTLFPTableau, ⊥, →(β, ⊥), H4) == true
@test alphasat(MVLTLFPTableau, ⊥, →(β, α), H4) == true
@test alphasat(MVLTLFPTableau, ⊥, →(β, β), H4) == true
@test alphasat(MVLTLFPTableau, ⊥, →(β, ⊤), H4) == true
@test alphasat(MVLTLFPTableau, ⊥, →(⊤, ⊥), H4) == true
@test alphasat(MVLTLFPTableau, ⊥, →(⊤, α), H4) == true
@test alphasat(MVLTLFPTableau, ⊥, →(⊤, β), H4) == true
@test alphasat(MVLTLFPTableau, ⊥, →(⊤, ⊤), H4) == true

@test alphasat(MVLTLFPTableau, α, →(⊥, ⊥), H4) == true
@test alphasat(MVLTLFPTableau, α, →(⊥, α), H4) == true
@test alphasat(MVLTLFPTableau, α, →(⊥, β), H4) == true
@test alphasat(MVLTLFPTableau, α, →(⊥, ⊤), H4) == true
@test alphasat(MVLTLFPTableau, α, →(α, ⊥), H4) == false
@test alphasat(MVLTLFPTableau, α, →(α, α), H4) == true
@test alphasat(MVLTLFPTableau, α, →(α, β), H4) == false
@test alphasat(MVLTLFPTableau, α, →(α, ⊤), H4) == true
@test alphasat(MVLTLFPTableau, α, →(β, ⊥), H4) == true
@test alphasat(MVLTLFPTableau, α, →(β, α), H4) == true
@test alphasat(MVLTLFPTableau, α, →(β, β), H4) == true
@test alphasat(MVLTLFPTableau, α, →(β, ⊤), H4) == true
@test alphasat(MVLTLFPTableau, α, →(⊤, ⊥), H4) == false
@test alphasat(MVLTLFPTableau, α, →(⊤, α), H4) == true
@test alphasat(MVLTLFPTableau, α, →(⊤, β), H4) == false
@test alphasat(MVLTLFPTableau, α, →(⊤, ⊤), H4) == true

@test alphasat(MVLTLFPTableau, β, →(⊥, ⊥), H4) == true
@test alphasat(MVLTLFPTableau, β, →(⊥, α), H4) == true
@test alphasat(MVLTLFPTableau, β, →(⊥, β), H4) == true
@test alphasat(MVLTLFPTableau, β, →(⊥, ⊤), H4) == true
@test alphasat(MVLTLFPTableau, β, →(α, ⊥), H4) == true
@test alphasat(MVLTLFPTableau, β, →(α, α), H4) == true
@test alphasat(MVLTLFPTableau, β, →(α, β), H4) == true
@test alphasat(MVLTLFPTableau, β, →(α, ⊤), H4) == true
@test alphasat(MVLTLFPTableau, β, →(β, ⊥), H4) == false
@test alphasat(MVLTLFPTableau, β, →(β, α), H4) == false
@test alphasat(MVLTLFPTableau, β, →(β, β), H4) == true
@test alphasat(MVLTLFPTableau, β, →(β, ⊤), H4) == true
@test alphasat(MVLTLFPTableau, β, →(⊤, ⊥), H4) == false
@test alphasat(MVLTLFPTableau, β, →(⊤, α), H4) == false
@test alphasat(MVLTLFPTableau, β, →(⊤, β), H4) == true
@test alphasat(MVLTLFPTableau, β, →(⊤, ⊤), H4) == true

@test alphasat(MVLTLFPTableau, ⊤, →(⊥, ⊥), H4) == true
@test alphasat(MVLTLFPTableau, ⊤, →(⊥, α), H4) == true
@test alphasat(MVLTLFPTableau, ⊤, →(⊥, β), H4) == true
@test alphasat(MVLTLFPTableau, ⊤, →(⊥, ⊤), H4) == true
@test alphasat(MVLTLFPTableau, ⊤, →(α, ⊥), H4) == false
@test alphasat(MVLTLFPTableau, ⊤, →(α, α), H4) == true
@test alphasat(MVLTLFPTableau, ⊤, →(α, β), H4) == false
@test alphasat(MVLTLFPTableau, ⊤, →(α, ⊤), H4) == true
@test alphasat(MVLTLFPTableau, ⊤, →(β, ⊥), H4) == false
@test alphasat(MVLTLFPTableau, ⊤, →(β, α), H4) == false
@test alphasat(MVLTLFPTableau, ⊤, →(β, β), H4) == true
@test alphasat(MVLTLFPTableau, ⊤, →(β, ⊤), H4) == true
@test alphasat(MVLTLFPTableau, ⊤, →(⊤, ⊥), H4) == false
@test alphasat(MVLTLFPTableau, ⊤, →(⊤, α), H4) == false
@test alphasat(MVLTLFPTableau, ⊤, →(⊤, β), H4) == false
@test alphasat(MVLTLFPTableau, ⊤, →(⊤, ⊤), H4) == true

@test alphasat(MVLTLFPTableau, ⊥, →(p, ⊥), H4) == true
@test alphasat(MVLTLFPTableau, ⊥, →(p, α), H4) == true
@test alphasat(MVLTLFPTableau, ⊥, →(p, β), H4) == true
@test alphasat(MVLTLFPTableau, ⊥, →(p, ⊤), H4) == true
@test alphasat(MVLTLFPTableau, α, →(p, ⊥), H4) == true
@test alphasat(MVLTLFPTableau, α, →(p, α), H4) == true
@test alphasat(MVLTLFPTableau, α, →(p, β), H4) == true
@test alphasat(MVLTLFPTableau, α, →(p, ⊤), H4) == true
@test alphasat(MVLTLFPTableau, β, →(p, ⊥), H4) == true
@test alphasat(MVLTLFPTableau, β, →(p, α), H4) == true
@test alphasat(MVLTLFPTableau, β, →(p, β), H4) == true
@test alphasat(MVLTLFPTableau, β, →(p, ⊤), H4) == true
@test alphasat(MVLTLFPTableau, ⊤, →(p, ⊥), H4) == true
@test alphasat(MVLTLFPTableau, ⊤, →(p, α), H4) == true
@test alphasat(MVLTLFPTableau, ⊤, →(p, β), H4) == true
@test alphasat(MVLTLFPTableau, ⊤, →(p, ⊤), H4) == true

@test alphasat(MVLTLFPTableau, ⊥, →(⊥, p), H4) == true
@test alphasat(MVLTLFPTableau, ⊥, →(α, p), H4) == true
@test alphasat(MVLTLFPTableau, ⊥, →(β, p), H4) == true
@test alphasat(MVLTLFPTableau, ⊥, →(⊤, p), H4) == true
@test alphasat(MVLTLFPTableau, α, →(⊥, p), H4) == true
@test alphasat(MVLTLFPTableau, α, →(α, p), H4) == true
@test alphasat(MVLTLFPTableau, α, →(β, p), H4) == true
@test alphasat(MVLTLFPTableau, α, →(⊤, p), H4) == true
@test alphasat(MVLTLFPTableau, β, →(⊥, p), H4) == true
@test alphasat(MVLTLFPTableau, β, →(α, p), H4) == true
@test alphasat(MVLTLFPTableau, β, →(β, p), H4) == true
@test alphasat(MVLTLFPTableau, β, →(⊤, p), H4) == true
@test alphasat(MVLTLFPTableau, ⊤, →(⊥, p), H4) == true
@test alphasat(MVLTLFPTableau, ⊤, →(α, p), H4) == true
@test alphasat(MVLTLFPTableau, ⊤, →(β, p), H4) == true
@test alphasat(MVLTLFPTableau, ⊤, →(⊤, p), H4) == true

@test alphasat(MVLTLFPTableau, ⊥, →(p, p), H4)
@test alphasat(MVLTLFPTableau, α, →(p, p), H4)
@test alphasat(MVLTLFPTableau, β, →(p, p), H4)
@test alphasat(MVLTLFPTableau, ⊤, →(p, p), H4)

@test alphasat(MVLTLFPTableau, ⊥, →(p, q), H4)
@test alphasat(MVLTLFPTableau, α, →(p, q), H4)
@test alphasat(MVLTLFPTableau, β, →(p, q), H4)
@test alphasat(MVLTLFPTableau, ⊤, →(p, q), H4)

@test alphasat(MVLTLFPTableau, ⊥, →(q, p), H4)
@test alphasat(MVLTLFPTableau, α, →(q, p), H4)
@test alphasat(MVLTLFPTableau, β, →(q, p), H4)
@test alphasat(MVLTLFPTableau, ⊤, →(q, p), H4)

################################################################################
#### More difficult formulas ###################################################
################################################################################

result = alphasat(MVLTLFPTableau, ⊤, booleantofuzzy(parseformula(
    "(x∨y∨z)∧(x∨y∨¬z)∧(x∨¬y∨z)∧(x∨¬y∨¬z)∧" *
    "(¬x∨y∨z)∧(¬x∨y∨¬z)∧(¬x∨¬y∨z)∧(¬x∨¬y∨¬z)"
)), H4, timeout=timeout)

if !isnothing(result)
    @test result == false
end
