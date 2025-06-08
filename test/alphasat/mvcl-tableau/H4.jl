################################################################################
#### H4 ########################################################################
################################################################################

using SoleLogics: CL_N, CL_S, CL_E, CL_W
using SoleLogics.ManyValuedLogics: H4
using SoleLogics.ManyValuedLogics: α, β

p, q = Atom.(["p", "q"])

diamondCL_N = diamond(CL_N)
diamondCL_S = diamond(CL_S)
diamondCL_E = diamond(CL_E)
diamondCL_W = diamond(CL_W)

boxCL_N = box(CL_N)
boxCL_S = box(CL_S)
boxCL_E = box(CL_E)
boxCL_W = box(CL_W)

timeout = 10

################################################################################
## Base cases ##################################################################
################################################################################

@test alphasat(MVCLTableau, ⊥, ⊥, H4) == true
@test alphasat(MVCLTableau, ⊥, α, H4) == true
@test alphasat(MVCLTableau, ⊥, β, H4) == true
@test alphasat(MVCLTableau, ⊥, ⊤, H4) == true
@test alphasat(MVCLTableau, α, ⊥, H4) == false
@test alphasat(MVCLTableau, α, α, H4) == true
@test alphasat(MVCLTableau, α, β, H4) == false
@test alphasat(MVCLTableau, α, ⊤, H4) == true
@test alphasat(MVCLTableau, β, ⊥, H4) == false
@test alphasat(MVCLTableau, β, α, H4) == false
@test alphasat(MVCLTableau, β, β, H4) == true
@test alphasat(MVCLTableau, β, ⊤, H4) == true
@test alphasat(MVCLTableau, ⊤, ⊥, H4) == false
@test alphasat(MVCLTableau, ⊤, α, H4) == false
@test alphasat(MVCLTableau, ⊤, β, H4) == false
@test alphasat(MVCLTableau, ⊤, ⊤, H4) == true

@test alphasat(MVCLTableau, ⊥, p, H4) == true
@test alphasat(MVCLTableau, α, p, H4) == true
@test alphasat(MVCLTableau, β, p, H4) == true
@test alphasat(MVCLTableau, ⊤, p, H4) == true

################################################################################
## (Strong) disjuction #########################################################
################################################################################

@test alphasat(MVCLTableau, ⊥, ∨(⊥, ⊥), H4) == true
@test alphasat(MVCLTableau, ⊥, ∨(⊥, α), H4) == true
@test alphasat(MVCLTableau, ⊥, ∨(⊥, β), H4) == true
@test alphasat(MVCLTableau, ⊥, ∨(⊥, ⊤), H4) == true
@test alphasat(MVCLTableau, ⊥, ∨(α, ⊥), H4) == true
@test alphasat(MVCLTableau, ⊥, ∨(α, α), H4) == true
@test alphasat(MVCLTableau, ⊥, ∨(α, β), H4) == true
@test alphasat(MVCLTableau, ⊥, ∨(α, ⊤), H4) == true
@test alphasat(MVCLTableau, ⊥, ∨(β, ⊥), H4) == true
@test alphasat(MVCLTableau, ⊥, ∨(β, α), H4) == true
@test alphasat(MVCLTableau, ⊥, ∨(β, β), H4) == true
@test alphasat(MVCLTableau, ⊥, ∨(β, ⊤), H4) == true
@test alphasat(MVCLTableau, ⊥, ∨(⊤, ⊥), H4) == true
@test alphasat(MVCLTableau, ⊥, ∨(⊤, α), H4) == true
@test alphasat(MVCLTableau, ⊥, ∨(⊤, β), H4) == true
@test alphasat(MVCLTableau, ⊥, ∨(⊤, ⊤), H4) == true

@test alphasat(MVCLTableau, α, ∨(⊥, ⊥), H4) == false
@test alphasat(MVCLTableau, α, ∨(⊥, α), H4) == true
@test alphasat(MVCLTableau, α, ∨(⊥, β), H4) == false
@test alphasat(MVCLTableau, α, ∨(⊥, ⊤), H4) == true
@test alphasat(MVCLTableau, α, ∨(α, ⊥), H4) == true
@test alphasat(MVCLTableau, α, ∨(α, α), H4) == true
@test alphasat(MVCLTableau, α, ∨(α, β), H4) == true
@test alphasat(MVCLTableau, α, ∨(α, ⊤), H4) == true
@test alphasat(MVCLTableau, α, ∨(β, ⊥), H4) == false
@test alphasat(MVCLTableau, α, ∨(β, α), H4) == true
@test alphasat(MVCLTableau, α, ∨(β, β), H4) == false
@test alphasat(MVCLTableau, α, ∨(β, ⊤), H4) == true
@test alphasat(MVCLTableau, α, ∨(⊤, ⊥), H4) == true
@test alphasat(MVCLTableau, α, ∨(⊤, α), H4) == true
@test alphasat(MVCLTableau, α, ∨(⊤, β), H4) == true
@test alphasat(MVCLTableau, α, ∨(⊤, ⊤), H4) == true

@test alphasat(MVCLTableau, β, ∨(⊥, ⊥), H4) == false
@test alphasat(MVCLTableau, β, ∨(⊥, α), H4) == false
@test alphasat(MVCLTableau, β, ∨(⊥, β), H4) == true
@test alphasat(MVCLTableau, β, ∨(⊥, ⊤), H4) == true
@test alphasat(MVCLTableau, β, ∨(α, ⊥), H4) == false
@test alphasat(MVCLTableau, β, ∨(α, α), H4) == false
@test alphasat(MVCLTableau, β, ∨(α, β), H4) == true
@test alphasat(MVCLTableau, β, ∨(α, ⊤), H4) == true
@test alphasat(MVCLTableau, β, ∨(β, ⊥), H4) == true
@test alphasat(MVCLTableau, β, ∨(β, α), H4) == true
@test alphasat(MVCLTableau, β, ∨(β, β), H4) == true
@test alphasat(MVCLTableau, β, ∨(β, ⊤), H4) == true
@test alphasat(MVCLTableau, β, ∨(⊤, ⊥), H4) == true
@test alphasat(MVCLTableau, β, ∨(⊤, α), H4) == true
@test alphasat(MVCLTableau, β, ∨(⊤, β), H4) == true
@test alphasat(MVCLTableau, β, ∨(⊤, ⊤), H4) == true

@test alphasat(MVCLTableau, ⊤, ∨(⊥, ⊥), H4) == false
@test alphasat(MVCLTableau, ⊤, ∨(⊥, α), H4) == false
@test alphasat(MVCLTableau, ⊤, ∨(⊥, β), H4) == false
@test alphasat(MVCLTableau, ⊤, ∨(⊥, ⊤), H4) == true
@test alphasat(MVCLTableau, ⊤, ∨(α, ⊥), H4) == false
@test alphasat(MVCLTableau, ⊤, ∨(α, α), H4) == false
@test alphasat(MVCLTableau, ⊤, ∨(α, β), H4) == true
@test alphasat(MVCLTableau, ⊤, ∨(α, ⊤), H4) == true
@test alphasat(MVCLTableau, ⊤, ∨(β, ⊥), H4) == false
@test alphasat(MVCLTableau, ⊤, ∨(β, α), H4) == true
@test alphasat(MVCLTableau, ⊤, ∨(β, β), H4) == false
@test alphasat(MVCLTableau, ⊤, ∨(β, ⊤), H4) == true
@test alphasat(MVCLTableau, ⊤, ∨(⊤, ⊥), H4) == true
@test alphasat(MVCLTableau, ⊤, ∨(⊤, α), H4) == true
@test alphasat(MVCLTableau, ⊤, ∨(⊤, β), H4) == true
@test alphasat(MVCLTableau, ⊤, ∨(⊤, ⊤), H4) == true

@test alphasat(MVCLTableau, ⊥, ∨(p, ⊥), H4) == true
@test alphasat(MVCLTableau, ⊥, ∨(p, α), H4) == true
@test alphasat(MVCLTableau, ⊥, ∨(p, β), H4) == true
@test alphasat(MVCLTableau, ⊥, ∨(p, ⊤), H4) == true
@test alphasat(MVCLTableau, α, ∨(p, ⊥), H4) == true
@test alphasat(MVCLTableau, α, ∨(p, α), H4) == true
@test alphasat(MVCLTableau, α, ∨(p, β), H4) == true
@test alphasat(MVCLTableau, α, ∨(p, ⊤), H4) == true
@test alphasat(MVCLTableau, β, ∨(p, ⊥), H4) == true
@test alphasat(MVCLTableau, β, ∨(p, α), H4) == true
@test alphasat(MVCLTableau, β, ∨(p, β), H4) == true
@test alphasat(MVCLTableau, β, ∨(p, ⊤), H4) == true
@test alphasat(MVCLTableau, ⊤, ∨(p, ⊥), H4) == true
@test alphasat(MVCLTableau, ⊤, ∨(p, α), H4) == true
@test alphasat(MVCLTableau, ⊤, ∨(p, β), H4) == true
@test alphasat(MVCLTableau, ⊤, ∨(p, ⊤), H4) == true

@test alphasat(MVCLTableau, ⊥, ∨(⊥, p), H4) == true
@test alphasat(MVCLTableau, ⊥, ∨(α, p), H4) == true
@test alphasat(MVCLTableau, ⊥, ∨(β, p), H4) == true
@test alphasat(MVCLTableau, ⊥, ∨(⊤, p), H4) == true
@test alphasat(MVCLTableau, α, ∨(⊥, p), H4) == true
@test alphasat(MVCLTableau, α, ∨(α, p), H4) == true
@test alphasat(MVCLTableau, α, ∨(β, p), H4) == true
@test alphasat(MVCLTableau, α, ∨(⊤, p), H4) == true
@test alphasat(MVCLTableau, β, ∨(⊥, p), H4) == true
@test alphasat(MVCLTableau, β, ∨(α, p), H4) == true
@test alphasat(MVCLTableau, β, ∨(β, p), H4) == true
@test alphasat(MVCLTableau, β, ∨(⊤, p), H4) == true
@test alphasat(MVCLTableau, ⊤, ∨(⊥, p), H4) == true
@test alphasat(MVCLTableau, ⊤, ∨(α, p), H4) == true
@test alphasat(MVCLTableau, ⊤, ∨(β, p), H4) == true
@test alphasat(MVCLTableau, ⊤, ∨(⊤, p), H4) == true

@test alphasat(MVCLTableau, ⊥, ∨(p, p), H4)
@test alphasat(MVCLTableau, α, ∨(p, p), H4)
@test alphasat(MVCLTableau, β, ∨(p, p), H4)
@test alphasat(MVCLTableau, ⊤, ∨(p, p), H4)

@test alphasat(MVCLTableau, ⊥, ∨(p, q), H4)
@test alphasat(MVCLTableau, α, ∨(p, q), H4)
@test alphasat(MVCLTableau, β, ∨(p, q), H4)
@test alphasat(MVCLTableau, ⊤, ∨(p, q), H4)

@test alphasat(MVCLTableau, ⊥, ∨(q, q), H4)
@test alphasat(MVCLTableau, α, ∨(q, q), H4)
@test alphasat(MVCLTableau, β, ∨(q, q), H4)
@test alphasat(MVCLTableau, ⊤, ∨(q, q), H4)

################################################################################
## (Strong) conjunction ########################################################
################################################################################

@test alphasat(MVCLTableau, ⊥, ∧(⊥, ⊥), H4) == true
@test alphasat(MVCLTableau, ⊥, ∧(⊥, α), H4) == true
@test alphasat(MVCLTableau, ⊥, ∧(⊥, β), H4) == true
@test alphasat(MVCLTableau, ⊥, ∧(⊥, ⊤), H4) == true
@test alphasat(MVCLTableau, ⊥, ∧(α, ⊥), H4) == true
@test alphasat(MVCLTableau, ⊥, ∧(α, α), H4) == true
@test alphasat(MVCLTableau, ⊥, ∧(α, β), H4) == true
@test alphasat(MVCLTableau, ⊥, ∧(α, ⊤), H4) == true
@test alphasat(MVCLTableau, ⊥, ∧(β, ⊥), H4) == true
@test alphasat(MVCLTableau, ⊥, ∧(β, α), H4) == true
@test alphasat(MVCLTableau, ⊥, ∧(β, β), H4) == true
@test alphasat(MVCLTableau, ⊥, ∧(β, ⊤), H4) == true
@test alphasat(MVCLTableau, ⊥, ∧(⊤, ⊥), H4) == true
@test alphasat(MVCLTableau, ⊥, ∧(⊤, α), H4) == true
@test alphasat(MVCLTableau, ⊥, ∧(⊤, β), H4) == true
@test alphasat(MVCLTableau, ⊥, ∧(⊤, ⊤), H4) == true

@test alphasat(MVCLTableau, α, ∧(⊥, ⊥), H4) == false
@test alphasat(MVCLTableau, α, ∧(⊥, α), H4) == false
@test alphasat(MVCLTableau, α, ∧(⊥, β), H4) == false
@test alphasat(MVCLTableau, α, ∧(⊥, ⊤), H4) == false
@test alphasat(MVCLTableau, α, ∧(α, ⊥), H4) == false
@test alphasat(MVCLTableau, α, ∧(α, α), H4) == true
@test alphasat(MVCLTableau, α, ∧(α, β), H4) == false
@test alphasat(MVCLTableau, α, ∧(α, ⊤), H4) == true
@test alphasat(MVCLTableau, α, ∧(β, ⊥), H4) == false
@test alphasat(MVCLTableau, α, ∧(β, α), H4) == false
@test alphasat(MVCLTableau, α, ∧(β, β), H4) == false
@test alphasat(MVCLTableau, α, ∧(β, ⊤), H4) == false
@test alphasat(MVCLTableau, α, ∧(⊤, ⊥), H4) == false
@test alphasat(MVCLTableau, α, ∧(⊤, α), H4) == true
@test alphasat(MVCLTableau, α, ∧(⊤, β), H4) == false
@test alphasat(MVCLTableau, α, ∧(⊤, ⊤), H4) == true

@test alphasat(MVCLTableau, β, ∧(⊥, ⊥), H4) == false
@test alphasat(MVCLTableau, β, ∧(⊥, α), H4) == false
@test alphasat(MVCLTableau, β, ∧(⊥, β), H4) == false
@test alphasat(MVCLTableau, β, ∧(⊥, ⊤), H4) == false
@test alphasat(MVCLTableau, β, ∧(α, ⊥), H4) == false
@test alphasat(MVCLTableau, β, ∧(α, α), H4) == false
@test alphasat(MVCLTableau, β, ∧(α, β), H4) == false
@test alphasat(MVCLTableau, β, ∧(α, ⊤), H4) == false
@test alphasat(MVCLTableau, β, ∧(β, ⊥), H4) == false
@test alphasat(MVCLTableau, β, ∧(β, α), H4) == false
@test alphasat(MVCLTableau, β, ∧(β, β), H4) == true
@test alphasat(MVCLTableau, β, ∧(β, ⊤), H4) == true
@test alphasat(MVCLTableau, β, ∧(⊤, ⊥), H4) == false
@test alphasat(MVCLTableau, β, ∧(⊤, α), H4) == false
@test alphasat(MVCLTableau, β, ∧(⊤, β), H4) == true
@test alphasat(MVCLTableau, β, ∧(⊤, ⊤), H4) == true

@test alphasat(MVCLTableau, ⊤, ∧(⊥, ⊥), H4) == false
@test alphasat(MVCLTableau, ⊤, ∧(⊥, α), H4) == false
@test alphasat(MVCLTableau, ⊤, ∧(⊥, β), H4) == false
@test alphasat(MVCLTableau, ⊤, ∧(⊥, ⊤), H4) == false
@test alphasat(MVCLTableau, ⊤, ∧(α, ⊥), H4) == false
@test alphasat(MVCLTableau, ⊤, ∧(α, α), H4) == false
@test alphasat(MVCLTableau, ⊤, ∧(α, β), H4) == false
@test alphasat(MVCLTableau, ⊤, ∧(α, ⊤), H4) == false
@test alphasat(MVCLTableau, ⊤, ∧(β, ⊥), H4) == false
@test alphasat(MVCLTableau, ⊤, ∧(β, α), H4) == false
@test alphasat(MVCLTableau, ⊤, ∧(β, β), H4) == false
@test alphasat(MVCLTableau, ⊤, ∧(β, ⊤), H4) == false
@test alphasat(MVCLTableau, ⊤, ∧(⊤, ⊥), H4) == false
@test alphasat(MVCLTableau, ⊤, ∧(⊤, α), H4) == false
@test alphasat(MVCLTableau, ⊤, ∧(⊤, β), H4) == false
@test alphasat(MVCLTableau, ⊤, ∧(⊤, ⊤), H4) == true

@test alphasat(MVCLTableau, ⊥, ∧(p, ⊥), H4) == true
@test alphasat(MVCLTableau, ⊥, ∧(p, α), H4) == true
@test alphasat(MVCLTableau, ⊥, ∧(p, β), H4) == true
@test alphasat(MVCLTableau, ⊥, ∧(p, ⊤), H4) == true
@test alphasat(MVCLTableau, α, ∧(p, ⊥), H4) == false
@test alphasat(MVCLTableau, α, ∧(p, α), H4) == true
@test alphasat(MVCLTableau, α, ∧(p, β), H4) == false
@test alphasat(MVCLTableau, α, ∧(p, ⊤), H4) == true
@test alphasat(MVCLTableau, β, ∧(p, ⊥), H4) == false
@test alphasat(MVCLTableau, β, ∧(p, α), H4) == false
@test alphasat(MVCLTableau, β, ∧(p, β), H4) == true
@test alphasat(MVCLTableau, β, ∧(p, ⊤), H4) == true
@test alphasat(MVCLTableau, ⊤, ∧(p, ⊥), H4) == false
@test alphasat(MVCLTableau, ⊤, ∧(p, α), H4) == false
@test alphasat(MVCLTableau, ⊤, ∧(p, β), H4) == false
@test alphasat(MVCLTableau, ⊤, ∧(p, ⊤), H4) == true

@test alphasat(MVCLTableau, ⊥, ∧(⊥, p), H4) == true
@test alphasat(MVCLTableau, ⊥, ∧(α, p), H4) == true
@test alphasat(MVCLTableau, ⊥, ∧(β, p), H4) == true
@test alphasat(MVCLTableau, ⊥, ∧(⊤, p), H4) == true
@test alphasat(MVCLTableau, α, ∧(⊥, p), H4) == false
@test alphasat(MVCLTableau, α, ∧(α, p), H4) == true
@test alphasat(MVCLTableau, α, ∧(β, p), H4) == false
@test alphasat(MVCLTableau, α, ∧(⊤, p), H4) == true
@test alphasat(MVCLTableau, β, ∧(⊥, p), H4) == false
@test alphasat(MVCLTableau, β, ∧(α, p), H4) == false
@test alphasat(MVCLTableau, β, ∧(β, p), H4) == true
@test alphasat(MVCLTableau, β, ∧(⊤, p), H4) == true
@test alphasat(MVCLTableau, ⊤, ∧(⊥, p), H4) == false
@test alphasat(MVCLTableau, ⊤, ∧(α, p), H4) == false
@test alphasat(MVCLTableau, ⊤, ∧(β, p), H4) == false
@test alphasat(MVCLTableau, ⊤, ∧(⊤, p), H4) == true

@test alphasat(MVCLTableau, ⊥, ∧(p, p), H4)
@test alphasat(MVCLTableau, α, ∧(p, p), H4)
@test alphasat(MVCLTableau, β, ∧(p, p), H4)
@test alphasat(MVCLTableau, ⊤, ∧(p, p), H4)

@test alphasat(MVCLTableau, ⊥, ∧(p, q), H4)
@test alphasat(MVCLTableau, α, ∧(p, q), H4)
@test alphasat(MVCLTableau, β, ∧(p, q), H4)
@test alphasat(MVCLTableau, ⊤, ∧(p, q), H4)

@test alphasat(MVCLTableau, ⊥, ∧(q, p), H4)
@test alphasat(MVCLTableau, α, ∧(q, p), H4)
@test alphasat(MVCLTableau, β, ∧(q, p), H4)
@test alphasat(MVCLTableau, ⊤, ∧(q, p), H4)

################################################################################
## Implication #################################################################
################################################################################

@test alphasat(MVCLTableau, ⊥, →(⊥, ⊥), H4) == true
@test alphasat(MVCLTableau, ⊥, →(⊥, α), H4) == true
@test alphasat(MVCLTableau, ⊥, →(⊥, β), H4) == true
@test alphasat(MVCLTableau, ⊥, →(⊥, ⊤), H4) == true
@test alphasat(MVCLTableau, ⊥, →(α, ⊥), H4) == true
@test alphasat(MVCLTableau, ⊥, →(α, α), H4) == true
@test alphasat(MVCLTableau, ⊥, →(α, β), H4) == true
@test alphasat(MVCLTableau, ⊥, →(α, ⊤), H4) == true
@test alphasat(MVCLTableau, ⊥, →(β, ⊥), H4) == true
@test alphasat(MVCLTableau, ⊥, →(β, α), H4) == true
@test alphasat(MVCLTableau, ⊥, →(β, β), H4) == true
@test alphasat(MVCLTableau, ⊥, →(β, ⊤), H4) == true
@test alphasat(MVCLTableau, ⊥, →(⊤, ⊥), H4) == true
@test alphasat(MVCLTableau, ⊥, →(⊤, α), H4) == true
@test alphasat(MVCLTableau, ⊥, →(⊤, β), H4) == true
@test alphasat(MVCLTableau, ⊥, →(⊤, ⊤), H4) == true

@test alphasat(MVCLTableau, α, →(⊥, ⊥), H4) == true
@test alphasat(MVCLTableau, α, →(⊥, α), H4) == true
@test alphasat(MVCLTableau, α, →(⊥, β), H4) == true
@test alphasat(MVCLTableau, α, →(⊥, ⊤), H4) == true
@test alphasat(MVCLTableau, α, →(α, ⊥), H4) == false
@test alphasat(MVCLTableau, α, →(α, α), H4) == true
@test alphasat(MVCLTableau, α, →(α, β), H4) == false
@test alphasat(MVCLTableau, α, →(α, ⊤), H4) == true
@test alphasat(MVCLTableau, α, →(β, ⊥), H4) == true
@test alphasat(MVCLTableau, α, →(β, α), H4) == true
@test alphasat(MVCLTableau, α, →(β, β), H4) == true
@test alphasat(MVCLTableau, α, →(β, ⊤), H4) == true
@test alphasat(MVCLTableau, α, →(⊤, ⊥), H4) == false
@test alphasat(MVCLTableau, α, →(⊤, α), H4) == true
@test alphasat(MVCLTableau, α, →(⊤, β), H4) == false
@test alphasat(MVCLTableau, α, →(⊤, ⊤), H4) == true

@test alphasat(MVCLTableau, β, →(⊥, ⊥), H4) == true
@test alphasat(MVCLTableau, β, →(⊥, α), H4) == true
@test alphasat(MVCLTableau, β, →(⊥, β), H4) == true
@test alphasat(MVCLTableau, β, →(⊥, ⊤), H4) == true
@test alphasat(MVCLTableau, β, →(α, ⊥), H4) == true
@test alphasat(MVCLTableau, β, →(α, α), H4) == true
@test alphasat(MVCLTableau, β, →(α, β), H4) == true
@test alphasat(MVCLTableau, β, →(α, ⊤), H4) == true
@test alphasat(MVCLTableau, β, →(β, ⊥), H4) == false
@test alphasat(MVCLTableau, β, →(β, α), H4) == false
@test alphasat(MVCLTableau, β, →(β, β), H4) == true
@test alphasat(MVCLTableau, β, →(β, ⊤), H4) == true
@test alphasat(MVCLTableau, β, →(⊤, ⊥), H4) == false
@test alphasat(MVCLTableau, β, →(⊤, α), H4) == false
@test alphasat(MVCLTableau, β, →(⊤, β), H4) == true
@test alphasat(MVCLTableau, β, →(⊤, ⊤), H4) == true

@test alphasat(MVCLTableau, ⊤, →(⊥, ⊥), H4) == true
@test alphasat(MVCLTableau, ⊤, →(⊥, α), H4) == true
@test alphasat(MVCLTableau, ⊤, →(⊥, β), H4) == true
@test alphasat(MVCLTableau, ⊤, →(⊥, ⊤), H4) == true
@test alphasat(MVCLTableau, ⊤, →(α, ⊥), H4) == false
@test alphasat(MVCLTableau, ⊤, →(α, α), H4) == true
@test alphasat(MVCLTableau, ⊤, →(α, β), H4) == false
@test alphasat(MVCLTableau, ⊤, →(α, ⊤), H4) == true
@test alphasat(MVCLTableau, ⊤, →(β, ⊥), H4) == false
@test alphasat(MVCLTableau, ⊤, →(β, α), H4) == false
@test alphasat(MVCLTableau, ⊤, →(β, β), H4) == true
@test alphasat(MVCLTableau, ⊤, →(β, ⊤), H4) == true
@test alphasat(MVCLTableau, ⊤, →(⊤, ⊥), H4) == false
@test alphasat(MVCLTableau, ⊤, →(⊤, α), H4) == false
@test alphasat(MVCLTableau, ⊤, →(⊤, β), H4) == false
@test alphasat(MVCLTableau, ⊤, →(⊤, ⊤), H4) == true

@test alphasat(MVCLTableau, ⊥, →(p, ⊥), H4) == true
@test alphasat(MVCLTableau, ⊥, →(p, α), H4) == true
@test alphasat(MVCLTableau, ⊥, →(p, β), H4) == true
@test alphasat(MVCLTableau, ⊥, →(p, ⊤), H4) == true
@test alphasat(MVCLTableau, α, →(p, ⊥), H4) == true
@test alphasat(MVCLTableau, α, →(p, α), H4) == true
@test alphasat(MVCLTableau, α, →(p, β), H4) == true
@test alphasat(MVCLTableau, α, →(p, ⊤), H4) == true
@test alphasat(MVCLTableau, β, →(p, ⊥), H4) == true
@test alphasat(MVCLTableau, β, →(p, α), H4) == true
@test alphasat(MVCLTableau, β, →(p, β), H4) == true
@test alphasat(MVCLTableau, β, →(p, ⊤), H4) == true
@test alphasat(MVCLTableau, ⊤, →(p, ⊥), H4) == true
@test alphasat(MVCLTableau, ⊤, →(p, α), H4) == true
@test alphasat(MVCLTableau, ⊤, →(p, β), H4) == true
@test alphasat(MVCLTableau, ⊤, →(p, ⊤), H4) == true

@test alphasat(MVCLTableau, ⊥, →(⊥, p), H4) == true
@test alphasat(MVCLTableau, ⊥, →(α, p), H4) == true
@test alphasat(MVCLTableau, ⊥, →(β, p), H4) == true
@test alphasat(MVCLTableau, ⊥, →(⊤, p), H4) == true
@test alphasat(MVCLTableau, α, →(⊥, p), H4) == true
@test alphasat(MVCLTableau, α, →(α, p), H4) == true
@test alphasat(MVCLTableau, α, →(β, p), H4) == true
@test alphasat(MVCLTableau, α, →(⊤, p), H4) == true
@test alphasat(MVCLTableau, β, →(⊥, p), H4) == true
@test alphasat(MVCLTableau, β, →(α, p), H4) == true
@test alphasat(MVCLTableau, β, →(β, p), H4) == true
@test alphasat(MVCLTableau, β, →(⊤, p), H4) == true
@test alphasat(MVCLTableau, ⊤, →(⊥, p), H4) == true
@test alphasat(MVCLTableau, ⊤, →(α, p), H4) == true
@test alphasat(MVCLTableau, ⊤, →(β, p), H4) == true
@test alphasat(MVCLTableau, ⊤, →(⊤, p), H4) == true

@test alphasat(MVCLTableau, ⊥, →(p, p), H4)
@test alphasat(MVCLTableau, α, →(p, p), H4)
@test alphasat(MVCLTableau, β, →(p, p), H4)
@test alphasat(MVCLTableau, ⊤, →(p, p), H4)

@test alphasat(MVCLTableau, ⊥, →(p, q), H4)
@test alphasat(MVCLTableau, α, →(p, q), H4)
@test alphasat(MVCLTableau, β, →(p, q), H4)
@test alphasat(MVCLTableau, ⊤, →(p, q), H4)

@test alphasat(MVCLTableau, ⊥, →(q, p), H4)
@test alphasat(MVCLTableau, α, →(q, p), H4)
@test alphasat(MVCLTableau, β, →(q, p), H4)
@test alphasat(MVCLTableau, ⊤, →(q, p), H4)

################################################################################
#### More difficult formulas ###################################################
################################################################################

result = alphasat(MVCLTableau, ⊤, booleantofuzzy(parseformula(
    "(x∨y∨z)∧(x∨y∨¬z)∧(x∨¬y∨z)∧(x∨¬y∨¬z)∧" *
    "(¬x∨y∨z)∧(¬x∨y∨¬z)∧(¬x∨¬y∨z)∧(¬x∨¬y∨¬z)"
)), H4, timeout=timeout)

if !isnothing(result)
    @test result == false
end

################################################################################
#### Modal cases ###############################################################
################################################################################

result = alphasat(
    MVCLTableau,
    ⊥,
    ∧(diamondCL_N(p), boxCL_N(→(p, ⊥))),
    H4,
    timeout=timeout
)

if !isnothing(result)
    @test result == true
end

result = alphasat(
    MVCLTableau,
    α,
    ∧(diamondCL_N(p), boxCL_N(→(p, ⊥))),
    H4,
    timeout=timeout
)

if !isnothing(result)
    @test result == false
end

result = alphasat(
    MVCLTableau,
    ⊤,
    ∧(diamondCL_N(p), boxCL_N(→(p, ⊥))),
    H4,
    timeout=timeout
)

if !isnothing(result)
    @test result == false
end

result = alphasat(
    MVCLTableau,
    ⊥,
    ∧(diamondCL_S(p), boxCL_S(→(p, ⊥))),
    H4,
    timeout=timeout
)

if !isnothing(result)
    @test result == true
end

result = alphasat(
    MVCLTableau,
    α,
    ∧(diamondCL_S(p), boxCL_S(→(p, ⊥))),
    H4,
    timeout=timeout
)

if !isnothing(result)
    @test result == false
end

result = alphasat(
    MVCLTableau,
    ⊤,
    ∧(diamondCL_S(p), boxCL_S(→(p, ⊥))),
    H4,
    timeout=timeout
)

if !isnothing(result)
    @test result == false
end

result = alphasat(
    MVCLTableau,
    ⊥,
    ∧(diamondCL_E(p), boxCL_E(→(p, ⊥))),
    H4,
    timeout=timeout
)

if !isnothing(result)
    @test result == true
end

result = alphasat(
    MVCLTableau,
    α,
    ∧(diamondCL_E(p), boxCL_E(→(p, ⊥))),
    H4,
    timeout=timeout
)

if !isnothing(result)
    @test result == false
end

result = alphasat(
    MVCLTableau,
    ⊤,
    ∧(diamondCL_E(p), boxCL_E(→(p, ⊥))),
    H4,
    timeout=timeout
)

if !isnothing(result)
    @test result == false
end

result = alphasat(
    MVCLTableau,
    ⊥,
    ∧(diamondCL_W(p), boxCL_W(→(p, ⊥))),
    H4,
    timeout=timeout
)

if !isnothing(result)
    @test result == true
end

result = alphasat(
    MVCLTableau,
    α,
    ∧(diamondCL_W(p), boxCL_W(→(p, ⊥))),
    H4,
    timeout=timeout
)

if !isnothing(result)
    @test result == false
end

result = alphasat(
    MVCLTableau,
    ⊤,
    ∧(diamondCL_W(p), boxCL_W(→(p, ⊥))),
    H4,
    timeout=timeout
)

if !isnothing(result)
    @test result == false
end
