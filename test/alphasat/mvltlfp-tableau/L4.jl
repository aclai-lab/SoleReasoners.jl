################################################################################
#### Ł4 ########################################################################
################################################################################

using SoleLogics.ManyValuedLogics: Ł4
using SoleLogics.ManyValuedLogics: α, β

p, q = Atom.(["p", "q"])

timeout = 60

################################################################################
## Base cases ##################################################################
################################################################################

@test alphasat(MVLTLFPTableau, ⊥, ⊥, Ł4) == true
@test alphasat(MVLTLFPTableau, ⊥, α, Ł4) == true
@test alphasat(MVLTLFPTableau, ⊥, β, Ł4) == true
@test alphasat(MVLTLFPTableau, ⊥, ⊤, Ł4) == true
@test alphasat(MVLTLFPTableau, α, ⊥, Ł4) == false
@test alphasat(MVLTLFPTableau, α, α, Ł4) == true
@test alphasat(MVLTLFPTableau, α, β, Ł4) == true
@test alphasat(MVLTLFPTableau, α, ⊤, Ł4) == true
@test alphasat(MVLTLFPTableau, β, ⊥, Ł4) == false
@test alphasat(MVLTLFPTableau, β, α, Ł4) == false
@test alphasat(MVLTLFPTableau, β, β, Ł4) == true
@test alphasat(MVLTLFPTableau, β, ⊤, Ł4) == true
@test alphasat(MVLTLFPTableau, ⊤, ⊥, Ł4) == false
@test alphasat(MVLTLFPTableau, ⊤, α, Ł4) == false
@test alphasat(MVLTLFPTableau, ⊤, β, Ł4) == false
@test alphasat(MVLTLFPTableau, ⊤, ⊤, Ł4) == true

@test alphasat(MVLTLFPTableau, ⊥, p, Ł4) == true
@test alphasat(MVLTLFPTableau, α, p, Ł4) == true
@test alphasat(MVLTLFPTableau, β, p, Ł4) == true
@test alphasat(MVLTLFPTableau, ⊤, p, Ł4) == true

################################################################################
## (Strong) disjuction #########################################################
################################################################################

@test alphasat(MVLTLFPTableau, ⊥, ∨(⊥, ⊥), Ł4) == true
@test alphasat(MVLTLFPTableau, ⊥, ∨(⊥, α), Ł4) == true
@test alphasat(MVLTLFPTableau, ⊥, ∨(⊥, β), Ł4) == true
@test alphasat(MVLTLFPTableau, ⊥, ∨(⊥, ⊤), Ł4) == true
@test alphasat(MVLTLFPTableau, ⊥, ∨(α, ⊥), Ł4) == true
@test alphasat(MVLTLFPTableau, ⊥, ∨(α, α), Ł4) == true
@test alphasat(MVLTLFPTableau, ⊥, ∨(α, β), Ł4) == true
@test alphasat(MVLTLFPTableau, ⊥, ∨(α, ⊤), Ł4) == true
@test alphasat(MVLTLFPTableau, ⊥, ∨(β, ⊥), Ł4) == true
@test alphasat(MVLTLFPTableau, ⊥, ∨(β, α), Ł4) == true
@test alphasat(MVLTLFPTableau, ⊥, ∨(β, β), Ł4) == true
@test alphasat(MVLTLFPTableau, ⊥, ∨(β, ⊤), Ł4) == true
@test alphasat(MVLTLFPTableau, ⊥, ∨(⊤, ⊥), Ł4) == true
@test alphasat(MVLTLFPTableau, ⊥, ∨(⊤, α), Ł4) == true
@test alphasat(MVLTLFPTableau, ⊥, ∨(⊤, β), Ł4) == true
@test alphasat(MVLTLFPTableau, ⊥, ∨(⊤, ⊤), Ł4) == true

@test alphasat(MVLTLFPTableau, α, ∨(⊥, ⊥), Ł4) == false
@test alphasat(MVLTLFPTableau, α, ∨(⊥, α), Ł4) == true
@test alphasat(MVLTLFPTableau, α, ∨(⊥, β), Ł4) == true
@test alphasat(MVLTLFPTableau, α, ∨(⊥, ⊤), Ł4) == true
@test alphasat(MVLTLFPTableau, α, ∨(α, ⊥), Ł4) == true
@test alphasat(MVLTLFPTableau, α, ∨(α, α), Ł4) == true
@test alphasat(MVLTLFPTableau, α, ∨(α, β), Ł4) == true
@test alphasat(MVLTLFPTableau, α, ∨(α, ⊤), Ł4) == true
@test alphasat(MVLTLFPTableau, α, ∨(β, ⊥), Ł4) == true
@test alphasat(MVLTLFPTableau, α, ∨(β, α), Ł4) == true
@test alphasat(MVLTLFPTableau, α, ∨(β, β), Ł4) == true
@test alphasat(MVLTLFPTableau, α, ∨(β, ⊤), Ł4) == true
@test alphasat(MVLTLFPTableau, α, ∨(⊤, ⊥), Ł4) == true
@test alphasat(MVLTLFPTableau, α, ∨(⊤, α), Ł4) == true
@test alphasat(MVLTLFPTableau, α, ∨(⊤, β), Ł4) == true
@test alphasat(MVLTLFPTableau, α, ∨(⊤, ⊤), Ł4) == true

@test alphasat(MVLTLFPTableau, β, ∨(⊥, ⊥), Ł4) == false
@test alphasat(MVLTLFPTableau, β, ∨(⊥, α), Ł4) == false
@test alphasat(MVLTLFPTableau, β, ∨(⊥, β), Ł4) == true
@test alphasat(MVLTLFPTableau, β, ∨(⊥, ⊤), Ł4) == true
@test alphasat(MVLTLFPTableau, β, ∨(α, ⊥), Ł4) == false
@test alphasat(MVLTLFPTableau, β, ∨(α, α), Ł4) == false
@test alphasat(MVLTLFPTableau, β, ∨(α, β), Ł4) == true
@test alphasat(MVLTLFPTableau, β, ∨(α, ⊤), Ł4) == true
@test alphasat(MVLTLFPTableau, β, ∨(β, ⊥), Ł4) == true
@test alphasat(MVLTLFPTableau, β, ∨(β, α), Ł4) == true
@test alphasat(MVLTLFPTableau, β, ∨(β, β), Ł4) == true
@test alphasat(MVLTLFPTableau, β, ∨(β, ⊤), Ł4) == true
@test alphasat(MVLTLFPTableau, β, ∨(⊤, ⊥), Ł4) == true
@test alphasat(MVLTLFPTableau, β, ∨(⊤, α), Ł4) == true
@test alphasat(MVLTLFPTableau, β, ∨(⊤, β), Ł4) == true
@test alphasat(MVLTLFPTableau, β, ∨(⊤, ⊤), Ł4) == true

@test alphasat(MVLTLFPTableau, ⊤, ∨(⊥, ⊥), Ł4) == false
@test alphasat(MVLTLFPTableau, ⊤, ∨(⊥, α), Ł4) == false
@test alphasat(MVLTLFPTableau, ⊤, ∨(⊥, β), Ł4) == false
@test alphasat(MVLTLFPTableau, ⊤, ∨(⊥, ⊤), Ł4) == true
@test alphasat(MVLTLFPTableau, ⊤, ∨(α, ⊥), Ł4) == false
@test alphasat(MVLTLFPTableau, ⊤, ∨(α, α), Ł4) == false
@test alphasat(MVLTLFPTableau, ⊤, ∨(α, β), Ł4) == false
@test alphasat(MVLTLFPTableau, ⊤, ∨(α, ⊤), Ł4) == true
@test alphasat(MVLTLFPTableau, ⊤, ∨(β, ⊥), Ł4) == false
@test alphasat(MVLTLFPTableau, ⊤, ∨(β, α), Ł4) == false
@test alphasat(MVLTLFPTableau, ⊤, ∨(β, β), Ł4) == false
@test alphasat(MVLTLFPTableau, ⊤, ∨(β, ⊤), Ł4) == true
@test alphasat(MVLTLFPTableau, ⊤, ∨(⊤, ⊥), Ł4) == true
@test alphasat(MVLTLFPTableau, ⊤, ∨(⊤, α), Ł4) == true
@test alphasat(MVLTLFPTableau, ⊤, ∨(⊤, β), Ł4) == true
@test alphasat(MVLTLFPTableau, ⊤, ∨(⊤, ⊤), Ł4) == true

@test alphasat(MVLTLFPTableau, ⊥, ∨(p, ⊥), Ł4) == true
@test alphasat(MVLTLFPTableau, ⊥, ∨(p, α), Ł4) == true
@test alphasat(MVLTLFPTableau, ⊥, ∨(p, β), Ł4) == true
@test alphasat(MVLTLFPTableau, ⊥, ∨(p, ⊤), Ł4) == true
@test alphasat(MVLTLFPTableau, α, ∨(p, ⊥), Ł4) == true
@test alphasat(MVLTLFPTableau, α, ∨(p, α), Ł4) == true
@test alphasat(MVLTLFPTableau, α, ∨(p, β), Ł4) == true
@test alphasat(MVLTLFPTableau, α, ∨(p, ⊤), Ł4) == true
@test alphasat(MVLTLFPTableau, β, ∨(p, ⊥), Ł4) == true
@test alphasat(MVLTLFPTableau, β, ∨(p, α), Ł4) == true
@test alphasat(MVLTLFPTableau, β, ∨(p, β), Ł4) == true
@test alphasat(MVLTLFPTableau, β, ∨(p, ⊤), Ł4) == true
@test alphasat(MVLTLFPTableau, ⊤, ∨(p, ⊥), Ł4) == true
@test alphasat(MVLTLFPTableau, ⊤, ∨(p, α), Ł4) == true
@test alphasat(MVLTLFPTableau, ⊤, ∨(p, β), Ł4) == true
@test alphasat(MVLTLFPTableau, ⊤, ∨(p, ⊤), Ł4) == true

@test alphasat(MVLTLFPTableau, ⊥, ∨(⊥, p), Ł4) == true
@test alphasat(MVLTLFPTableau, ⊥, ∨(α, p), Ł4) == true
@test alphasat(MVLTLFPTableau, ⊥, ∨(β, p), Ł4) == true
@test alphasat(MVLTLFPTableau, ⊥, ∨(⊤, p), Ł4) == true
@test alphasat(MVLTLFPTableau, α, ∨(⊥, p), Ł4) == true
@test alphasat(MVLTLFPTableau, α, ∨(α, p), Ł4) == true
@test alphasat(MVLTLFPTableau, α, ∨(β, p), Ł4) == true
@test alphasat(MVLTLFPTableau, α, ∨(⊤, p), Ł4) == true
@test alphasat(MVLTLFPTableau, β, ∨(⊥, p), Ł4) == true
@test alphasat(MVLTLFPTableau, β, ∨(α, p), Ł4) == true
@test alphasat(MVLTLFPTableau, β, ∨(β, p), Ł4) == true
@test alphasat(MVLTLFPTableau, β, ∨(⊤, p), Ł4) == true
@test alphasat(MVLTLFPTableau, ⊤, ∨(⊥, p), Ł4) == true
@test alphasat(MVLTLFPTableau, ⊤, ∨(α, p), Ł4) == true
@test alphasat(MVLTLFPTableau, ⊤, ∨(β, p), Ł4) == true
@test alphasat(MVLTLFPTableau, ⊤, ∨(⊤, p), Ł4) == true

@test alphasat(MVLTLFPTableau, ⊥, ∨(p, p), Ł4)
@test alphasat(MVLTLFPTableau, α, ∨(p, p), Ł4)
@test alphasat(MVLTLFPTableau, β, ∨(p, p), Ł4)
@test alphasat(MVLTLFPTableau, ⊤, ∨(p, p), Ł4)

@test alphasat(MVLTLFPTableau, ⊥, ∨(p, q), Ł4)
@test alphasat(MVLTLFPTableau, α, ∨(p, q), Ł4)
@test alphasat(MVLTLFPTableau, β, ∨(p, q), Ł4)
@test alphasat(MVLTLFPTableau, ⊤, ∨(p, q), Ł4)

@test alphasat(MVLTLFPTableau, ⊥, ∨(q, q), Ł4)
@test alphasat(MVLTLFPTableau, α, ∨(q, q), Ł4)
@test alphasat(MVLTLFPTableau, β, ∨(q, q), Ł4)
@test alphasat(MVLTLFPTableau, ⊤, ∨(q, q), Ł4)

################################################################################
## (Strong) conjunction ########################################################
################################################################################

@test alphasat(MVLTLFPTableau, ⊥, ∧(⊥, ⊥), Ł4) == true
@test alphasat(MVLTLFPTableau, ⊥, ∧(⊥, α), Ł4) == true
@test alphasat(MVLTLFPTableau, ⊥, ∧(⊥, β), Ł4) == true
@test alphasat(MVLTLFPTableau, ⊥, ∧(⊥, ⊤), Ł4) == true
@test alphasat(MVLTLFPTableau, ⊥, ∧(α, ⊥), Ł4) == true
@test alphasat(MVLTLFPTableau, ⊥, ∧(α, α), Ł4) == true
@test alphasat(MVLTLFPTableau, ⊥, ∧(α, β), Ł4) == true
@test alphasat(MVLTLFPTableau, ⊥, ∧(α, ⊤), Ł4) == true
@test alphasat(MVLTLFPTableau, ⊥, ∧(β, ⊥), Ł4) == true
@test alphasat(MVLTLFPTableau, ⊥, ∧(β, α), Ł4) == true
@test alphasat(MVLTLFPTableau, ⊥, ∧(β, β), Ł4) == true
@test alphasat(MVLTLFPTableau, ⊥, ∧(β, ⊤), Ł4) == true
@test alphasat(MVLTLFPTableau, ⊥, ∧(⊤, ⊥), Ł4) == true
@test alphasat(MVLTLFPTableau, ⊥, ∧(⊤, α), Ł4) == true
@test alphasat(MVLTLFPTableau, ⊥, ∧(⊤, β), Ł4) == true
@test alphasat(MVLTLFPTableau, ⊥, ∧(⊤, ⊤), Ł4) == true

@test alphasat(MVLTLFPTableau, α, ∧(⊥, ⊥), Ł4) == false
@test alphasat(MVLTLFPTableau, α, ∧(⊥, α), Ł4) == false
@test alphasat(MVLTLFPTableau, α, ∧(⊥, β), Ł4) == false
@test alphasat(MVLTLFPTableau, α, ∧(⊥, ⊤), Ł4) == false
@test alphasat(MVLTLFPTableau, α, ∧(α, ⊥), Ł4) == false
@test alphasat(MVLTLFPTableau, α, ∧(α, α), Ł4) == false
@test alphasat(MVLTLFPTableau, α, ∧(α, β), Ł4) == false
@test alphasat(MVLTLFPTableau, α, ∧(α, ⊤), Ł4) == true
@test alphasat(MVLTLFPTableau, α, ∧(β, ⊥), Ł4) == false
@test alphasat(MVLTLFPTableau, α, ∧(β, α), Ł4) == false
@test alphasat(MVLTLFPTableau, α, ∧(β, β), Ł4) == true
@test alphasat(MVLTLFPTableau, α, ∧(β, ⊤), Ł4) == true
@test alphasat(MVLTLFPTableau, α, ∧(⊤, ⊥), Ł4) == false
@test alphasat(MVLTLFPTableau, α, ∧(⊤, α), Ł4) == true
@test alphasat(MVLTLFPTableau, α, ∧(⊤, β), Ł4) == true
@test alphasat(MVLTLFPTableau, α, ∧(⊤, ⊤), Ł4) == true

@test alphasat(MVLTLFPTableau, β, ∧(⊥, ⊥), Ł4) == false
@test alphasat(MVLTLFPTableau, β, ∧(⊥, α), Ł4) == false
@test alphasat(MVLTLFPTableau, β, ∧(⊥, β), Ł4) == false
@test alphasat(MVLTLFPTableau, β, ∧(⊥, ⊤), Ł4) == false
@test alphasat(MVLTLFPTableau, β, ∧(α, ⊥), Ł4) == false
@test alphasat(MVLTLFPTableau, β, ∧(α, α), Ł4) == false
@test alphasat(MVLTLFPTableau, β, ∧(α, β), Ł4) == false
@test alphasat(MVLTLFPTableau, β, ∧(α, ⊤), Ł4) == false
@test alphasat(MVLTLFPTableau, β, ∧(β, ⊥), Ł4) == false
@test alphasat(MVLTLFPTableau, β, ∧(β, α), Ł4) == false
@test alphasat(MVLTLFPTableau, β, ∧(β, β), Ł4) == false
@test alphasat(MVLTLFPTableau, β, ∧(β, ⊤), Ł4) == true
@test alphasat(MVLTLFPTableau, β, ∧(⊤, ⊥), Ł4) == false
@test alphasat(MVLTLFPTableau, β, ∧(⊤, α), Ł4) == false
@test alphasat(MVLTLFPTableau, β, ∧(⊤, β), Ł4) == true
@test alphasat(MVLTLFPTableau, β, ∧(⊤, ⊤), Ł4) == true

@test alphasat(MVLTLFPTableau, ⊤, ∧(⊥, ⊥), Ł4) == false
@test alphasat(MVLTLFPTableau, ⊤, ∧(⊥, α), Ł4) == false
@test alphasat(MVLTLFPTableau, ⊤, ∧(⊥, β), Ł4) == false
@test alphasat(MVLTLFPTableau, ⊤, ∧(⊥, ⊤), Ł4) == false
@test alphasat(MVLTLFPTableau, ⊤, ∧(α, ⊥), Ł4) == false
@test alphasat(MVLTLFPTableau, ⊤, ∧(α, α), Ł4) == false
@test alphasat(MVLTLFPTableau, ⊤, ∧(α, β), Ł4) == false
@test alphasat(MVLTLFPTableau, ⊤, ∧(α, ⊤), Ł4) == false
@test alphasat(MVLTLFPTableau, ⊤, ∧(β, ⊥), Ł4) == false
@test alphasat(MVLTLFPTableau, ⊤, ∧(β, α), Ł4) == false
@test alphasat(MVLTLFPTableau, ⊤, ∧(β, β), Ł4) == false
@test alphasat(MVLTLFPTableau, ⊤, ∧(β, ⊤), Ł4) == false
@test alphasat(MVLTLFPTableau, ⊤, ∧(⊤, ⊥), Ł4) == false
@test alphasat(MVLTLFPTableau, ⊤, ∧(⊤, α), Ł4) == false
@test alphasat(MVLTLFPTableau, ⊤, ∧(⊤, β), Ł4) == false
@test alphasat(MVLTLFPTableau, ⊤, ∧(⊤, ⊤), Ł4) == true

@test alphasat(MVLTLFPTableau, ⊥, ∧(p, ⊥), Ł4) == true
@test alphasat(MVLTLFPTableau, ⊥, ∧(p, α), Ł4) == true
@test alphasat(MVLTLFPTableau, ⊥, ∧(p, β), Ł4) == true
@test alphasat(MVLTLFPTableau, ⊥, ∧(p, ⊤), Ł4) == true
@test alphasat(MVLTLFPTableau, α, ∧(p, ⊥), Ł4) == false
@test alphasat(MVLTLFPTableau, α, ∧(p, α), Ł4) == true
@test alphasat(MVLTLFPTableau, α, ∧(p, β), Ł4) == true
@test alphasat(MVLTLFPTableau, α, ∧(p, ⊤), Ł4) == true
@test alphasat(MVLTLFPTableau, β, ∧(p, ⊥), Ł4) == false
@test alphasat(MVLTLFPTableau, β, ∧(p, α), Ł4) == false
@test alphasat(MVLTLFPTableau, β, ∧(p, β), Ł4) == true
@test alphasat(MVLTLFPTableau, β, ∧(p, ⊤), Ł4) == true
@test alphasat(MVLTLFPTableau, ⊤, ∧(p, ⊥), Ł4) == false
@test alphasat(MVLTLFPTableau, ⊤, ∧(p, α), Ł4) == false
@test alphasat(MVLTLFPTableau, ⊤, ∧(p, β), Ł4) == false
@test alphasat(MVLTLFPTableau, ⊤, ∧(p, ⊤), Ł4) == true

@test alphasat(MVLTLFPTableau, ⊥, ∧(⊥, p), Ł4) == true
@test alphasat(MVLTLFPTableau, ⊥, ∧(α, p), Ł4) == true
@test alphasat(MVLTLFPTableau, ⊥, ∧(β, p), Ł4) == true
@test alphasat(MVLTLFPTableau, ⊥, ∧(⊤, p), Ł4) == true
@test alphasat(MVLTLFPTableau, α, ∧(⊥, p), Ł4) == false
@test alphasat(MVLTLFPTableau, α, ∧(α, p), Ł4) == true
@test alphasat(MVLTLFPTableau, α, ∧(β, p), Ł4) == true
@test alphasat(MVLTLFPTableau, α, ∧(⊤, p), Ł4) == true
@test alphasat(MVLTLFPTableau, β, ∧(⊥, p), Ł4) == false
@test alphasat(MVLTLFPTableau, β, ∧(α, p), Ł4) == false
@test alphasat(MVLTLFPTableau, β, ∧(β, p), Ł4) == true
@test alphasat(MVLTLFPTableau, β, ∧(⊤, p), Ł4) == true
@test alphasat(MVLTLFPTableau, ⊤, ∧(⊥, p), Ł4) == false
@test alphasat(MVLTLFPTableau, ⊤, ∧(α, p), Ł4) == false
@test alphasat(MVLTLFPTableau, ⊤, ∧(β, p), Ł4) == false
@test alphasat(MVLTLFPTableau, ⊤, ∧(⊤, p), Ł4) == true

@test alphasat(MVLTLFPTableau, ⊥, ∧(p, p), Ł4)
@test alphasat(MVLTLFPTableau, α, ∧(p, p), Ł4)
@test alphasat(MVLTLFPTableau, β, ∧(p, p), Ł4)
@test alphasat(MVLTLFPTableau, ⊤, ∧(p, p), Ł4)

@test alphasat(MVLTLFPTableau, ⊥, ∧(p, q), Ł4)
@test alphasat(MVLTLFPTableau, α, ∧(p, q), Ł4)
@test alphasat(MVLTLFPTableau, β, ∧(p, q), Ł4)
@test alphasat(MVLTLFPTableau, ⊤, ∧(p, q), Ł4)

@test alphasat(MVLTLFPTableau, ⊥, ∧(q, p), Ł4)
@test alphasat(MVLTLFPTableau, α, ∧(q, p), Ł4)
@test alphasat(MVLTLFPTableau, β, ∧(q, p), Ł4)
@test alphasat(MVLTLFPTableau, ⊤, ∧(q, p), Ł4)

################################################################################
## Implication #################################################################
################################################################################

@test alphasat(MVLTLFPTableau, ⊥, →(⊥, ⊥), Ł4) == true
@test alphasat(MVLTLFPTableau, ⊥, →(⊥, α), Ł4) == true
@test alphasat(MVLTLFPTableau, ⊥, →(⊥, β), Ł4) == true
@test alphasat(MVLTLFPTableau, ⊥, →(⊥, ⊤), Ł4) == true
@test alphasat(MVLTLFPTableau, ⊥, →(α, ⊥), Ł4) == true
@test alphasat(MVLTLFPTableau, ⊥, →(α, α), Ł4) == true
@test alphasat(MVLTLFPTableau, ⊥, →(α, β), Ł4) == true
@test alphasat(MVLTLFPTableau, ⊥, →(α, ⊤), Ł4) == true
@test alphasat(MVLTLFPTableau, ⊥, →(β, ⊥), Ł4) == true
@test alphasat(MVLTLFPTableau, ⊥, →(β, α), Ł4) == true
@test alphasat(MVLTLFPTableau, ⊥, →(β, β), Ł4) == true
@test alphasat(MVLTLFPTableau, ⊥, →(β, ⊤), Ł4) == true
@test alphasat(MVLTLFPTableau, ⊥, →(⊤, ⊥), Ł4) == true
@test alphasat(MVLTLFPTableau, ⊥, →(⊤, α), Ł4) == true
@test alphasat(MVLTLFPTableau, ⊥, →(⊤, β), Ł4) == true
@test alphasat(MVLTLFPTableau, ⊥, →(⊤, ⊤), Ł4) == true

@test alphasat(MVLTLFPTableau, α, →(⊥, ⊥), Ł4) == true
@test alphasat(MVLTLFPTableau, α, →(⊥, α), Ł4) == true
@test alphasat(MVLTLFPTableau, α, →(⊥, β), Ł4) == true
@test alphasat(MVLTLFPTableau, α, →(⊥, ⊤), Ł4) == true
@test alphasat(MVLTLFPTableau, α, →(α, ⊥), Ł4) == true
@test alphasat(MVLTLFPTableau, α, →(α, α), Ł4) == true
@test alphasat(MVLTLFPTableau, α, →(α, β), Ł4) == true
@test alphasat(MVLTLFPTableau, α, →(α, ⊤), Ł4) == true
@test alphasat(MVLTLFPTableau, α, →(β, ⊥), Ł4) == true
@test alphasat(MVLTLFPTableau, α, →(β, α), Ł4) == true
@test alphasat(MVLTLFPTableau, α, →(β, β), Ł4) == true
@test alphasat(MVLTLFPTableau, α, →(β, ⊤), Ł4) == true
@test alphasat(MVLTLFPTableau, α, →(⊤, ⊥), Ł4) == false
@test alphasat(MVLTLFPTableau, α, →(⊤, α), Ł4) == true
@test alphasat(MVLTLFPTableau, α, →(⊤, β), Ł4) == true
@test alphasat(MVLTLFPTableau, α, →(⊤, ⊤), Ł4) == true

@test alphasat(MVLTLFPTableau, β, →(⊥, ⊥), Ł4) == true
@test alphasat(MVLTLFPTableau, β, →(⊥, α), Ł4) == true
@test alphasat(MVLTLFPTableau, β, →(⊥, β), Ł4) == true
@test alphasat(MVLTLFPTableau, β, →(⊥, ⊤), Ł4) == true
@test alphasat(MVLTLFPTableau, β, →(α, ⊥), Ł4) == true
@test alphasat(MVLTLFPTableau, β, →(α, α), Ł4) == true
@test alphasat(MVLTLFPTableau, β, →(α, β), Ł4) == true
@test alphasat(MVLTLFPTableau, β, →(α, ⊤), Ł4) == true
@test alphasat(MVLTLFPTableau, β, →(β, ⊥), Ł4) == false
@test alphasat(MVLTLFPTableau, β, →(β, α), Ł4) == true
@test alphasat(MVLTLFPTableau, β, →(β, β), Ł4) == true
@test alphasat(MVLTLFPTableau, β, →(β, ⊤), Ł4) == true
@test alphasat(MVLTLFPTableau, β, →(⊤, ⊥), Ł4) == false
@test alphasat(MVLTLFPTableau, β, →(⊤, α), Ł4) == false
@test alphasat(MVLTLFPTableau, β, →(⊤, β), Ł4) == true
@test alphasat(MVLTLFPTableau, β, →(⊤, ⊤), Ł4) == true

@test alphasat(MVLTLFPTableau, ⊤, →(⊥, ⊥), Ł4) == true
@test alphasat(MVLTLFPTableau, ⊤, →(⊥, α), Ł4) == true
@test alphasat(MVLTLFPTableau, ⊤, →(⊥, β), Ł4) == true
@test alphasat(MVLTLFPTableau, ⊤, →(⊥, ⊤), Ł4) == true
@test alphasat(MVLTLFPTableau, ⊤, →(α, ⊥), Ł4) == false
@test alphasat(MVLTLFPTableau, ⊤, →(α, α), Ł4) == true
@test alphasat(MVLTLFPTableau, ⊤, →(α, β), Ł4) == true
@test alphasat(MVLTLFPTableau, ⊤, →(α, ⊤), Ł4) == true
@test alphasat(MVLTLFPTableau, ⊤, →(β, ⊥), Ł4) == false
@test alphasat(MVLTLFPTableau, ⊤, →(β, α), Ł4) == false
@test alphasat(MVLTLFPTableau, ⊤, →(β, β), Ł4) == true
@test alphasat(MVLTLFPTableau, ⊤, →(β, ⊤), Ł4) == true
@test alphasat(MVLTLFPTableau, ⊤, →(⊤, ⊥), Ł4) == false
@test alphasat(MVLTLFPTableau, ⊤, →(⊤, α), Ł4) == false
@test alphasat(MVLTLFPTableau, ⊤, →(⊤, β), Ł4) == false
@test alphasat(MVLTLFPTableau, ⊤, →(⊤, ⊤), Ł4) == true

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
)), Ł4, timeout=timeout)

if !isnothing(result)
    @test result == false
end
