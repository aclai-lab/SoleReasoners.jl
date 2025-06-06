################################################################################
#### H4 ########################################################################
################################################################################

using SoleLogics: LRCC8_Rec_DC, LRCC8_Rec_EC, LRCC8_Rec_PO
using SoleLogics: LRCC8_Rec_TPP, LRCC8_Rec_TPPi, LRCC8_Rec_NTPP, LRCC8_Rec_NTPPi
using SoleLogics.ManyValuedLogics: H4
using SoleLogics.ManyValuedLogics: α, β

p, q = Atom.(["p", "q"])

diamondLRCC8_Rec_DC    = diamond(LRCC8_Rec_DC)
diamondLRCC8_Rec_EC    = diamond(LRCC8_Rec_EC)
diamondLRCC8_Rec_PO    = diamond(LRCC8_Rec_PO)
diamondLRCC8_Rec_TPP   = diamond(LRCC8_Rec_TPP)
diamondLRCC8_Rec_TPPi  = diamond(LRCC8_Rec_TPPi)
diamondLRCC8_Rec_NTPP  = diamond(LRCC8_Rec_NTPP)
diamondLRCC8_Rec_NTPPi = diamond(LRCC8_Rec_NTPPi)

boxLRCC8_Rec_DC    = box(LRCC8_Rec_DC)
boxLRCC8_Rec_EC    = box(LRCC8_Rec_EC)
boxLRCC8_Rec_PO    = box(LRCC8_Rec_PO)
boxLRCC8_Rec_TPP   = box(LRCC8_Rec_TPP)
boxLRCC8_Rec_TPPi  = box(LRCC8_Rec_TPPi)
boxLRCC8_Rec_NTPP  = box(LRCC8_Rec_NTPP)
boxLRCC8_Rec_NTPPi = box(LRCC8_Rec_NTPPi)

timeout = 30

################################################################################
## Base cases ##################################################################
################################################################################

@test alphasat(MVLRCC8Tableau, ⊥, ⊥, H4) == true
@test alphasat(MVLRCC8Tableau, ⊥, α, H4) == true
@test alphasat(MVLRCC8Tableau, ⊥, β, H4) == true
@test alphasat(MVLRCC8Tableau, ⊥, ⊤, H4) == true
@test alphasat(MVLRCC8Tableau, α, ⊥, H4) == false
@test alphasat(MVLRCC8Tableau, α, α, H4) == true
@test alphasat(MVLRCC8Tableau, α, β, H4) == false
@test alphasat(MVLRCC8Tableau, α, ⊤, H4) == true
@test alphasat(MVLRCC8Tableau, β, ⊥, H4) == false
@test alphasat(MVLRCC8Tableau, β, α, H4) == false
@test alphasat(MVLRCC8Tableau, β, β, H4) == true
@test alphasat(MVLRCC8Tableau, β, ⊤, H4) == true
@test alphasat(MVLRCC8Tableau, ⊤, ⊥, H4) == false
@test alphasat(MVLRCC8Tableau, ⊤, α, H4) == false
@test alphasat(MVLRCC8Tableau, ⊤, β, H4) == false
@test alphasat(MVLRCC8Tableau, ⊤, ⊤, H4) == true

@test alphasat(MVLRCC8Tableau, ⊥, p, H4) == true
@test alphasat(MVLRCC8Tableau, α, p, H4) == true
@test alphasat(MVLRCC8Tableau, β, p, H4) == true
@test alphasat(MVLRCC8Tableau, ⊤, p, H4) == true

################################################################################
## (Strong) disjuction #########################################################
################################################################################

@test alphasat(MVLRCC8Tableau, ⊥, ∨(⊥, ⊥), H4) == true
@test alphasat(MVLRCC8Tableau, ⊥, ∨(⊥, α), H4) == true
@test alphasat(MVLRCC8Tableau, ⊥, ∨(⊥, β), H4) == true
@test alphasat(MVLRCC8Tableau, ⊥, ∨(⊥, ⊤), H4) == true
@test alphasat(MVLRCC8Tableau, ⊥, ∨(α, ⊥), H4) == true
@test alphasat(MVLRCC8Tableau, ⊥, ∨(α, α), H4) == true
@test alphasat(MVLRCC8Tableau, ⊥, ∨(α, β), H4) == true
@test alphasat(MVLRCC8Tableau, ⊥, ∨(α, ⊤), H4) == true
@test alphasat(MVLRCC8Tableau, ⊥, ∨(β, ⊥), H4) == true
@test alphasat(MVLRCC8Tableau, ⊥, ∨(β, α), H4) == true
@test alphasat(MVLRCC8Tableau, ⊥, ∨(β, β), H4) == true
@test alphasat(MVLRCC8Tableau, ⊥, ∨(β, ⊤), H4) == true
@test alphasat(MVLRCC8Tableau, ⊥, ∨(⊤, ⊥), H4) == true
@test alphasat(MVLRCC8Tableau, ⊥, ∨(⊤, α), H4) == true
@test alphasat(MVLRCC8Tableau, ⊥, ∨(⊤, β), H4) == true
@test alphasat(MVLRCC8Tableau, ⊥, ∨(⊤, ⊤), H4) == true

@test alphasat(MVLRCC8Tableau, α, ∨(⊥, ⊥), H4) == false
@test alphasat(MVLRCC8Tableau, α, ∨(⊥, α), H4) == true
@test alphasat(MVLRCC8Tableau, α, ∨(⊥, β), H4) == false
@test alphasat(MVLRCC8Tableau, α, ∨(⊥, ⊤), H4) == true
@test alphasat(MVLRCC8Tableau, α, ∨(α, ⊥), H4) == true
@test alphasat(MVLRCC8Tableau, α, ∨(α, α), H4) == true
@test alphasat(MVLRCC8Tableau, α, ∨(α, β), H4) == true
@test alphasat(MVLRCC8Tableau, α, ∨(α, ⊤), H4) == true
@test alphasat(MVLRCC8Tableau, α, ∨(β, ⊥), H4) == false
@test alphasat(MVLRCC8Tableau, α, ∨(β, α), H4) == true
@test alphasat(MVLRCC8Tableau, α, ∨(β, β), H4) == false
@test alphasat(MVLRCC8Tableau, α, ∨(β, ⊤), H4) == true
@test alphasat(MVLRCC8Tableau, α, ∨(⊤, ⊥), H4) == true
@test alphasat(MVLRCC8Tableau, α, ∨(⊤, α), H4) == true
@test alphasat(MVLRCC8Tableau, α, ∨(⊤, β), H4) == true
@test alphasat(MVLRCC8Tableau, α, ∨(⊤, ⊤), H4) == true

@test alphasat(MVLRCC8Tableau, β, ∨(⊥, ⊥), H4) == false
@test alphasat(MVLRCC8Tableau, β, ∨(⊥, α), H4) == false
@test alphasat(MVLRCC8Tableau, β, ∨(⊥, β), H4) == true
@test alphasat(MVLRCC8Tableau, β, ∨(⊥, ⊤), H4) == true
@test alphasat(MVLRCC8Tableau, β, ∨(α, ⊥), H4) == false
@test alphasat(MVLRCC8Tableau, β, ∨(α, α), H4) == false
@test alphasat(MVLRCC8Tableau, β, ∨(α, β), H4) == true
@test alphasat(MVLRCC8Tableau, β, ∨(α, ⊤), H4) == true
@test alphasat(MVLRCC8Tableau, β, ∨(β, ⊥), H4) == true
@test alphasat(MVLRCC8Tableau, β, ∨(β, α), H4) == true
@test alphasat(MVLRCC8Tableau, β, ∨(β, β), H4) == true
@test alphasat(MVLRCC8Tableau, β, ∨(β, ⊤), H4) == true
@test alphasat(MVLRCC8Tableau, β, ∨(⊤, ⊥), H4) == true
@test alphasat(MVLRCC8Tableau, β, ∨(⊤, α), H4) == true
@test alphasat(MVLRCC8Tableau, β, ∨(⊤, β), H4) == true
@test alphasat(MVLRCC8Tableau, β, ∨(⊤, ⊤), H4) == true

@test alphasat(MVLRCC8Tableau, ⊤, ∨(⊥, ⊥), H4) == false
@test alphasat(MVLRCC8Tableau, ⊤, ∨(⊥, α), H4) == false
@test alphasat(MVLRCC8Tableau, ⊤, ∨(⊥, β), H4) == false
@test alphasat(MVLRCC8Tableau, ⊤, ∨(⊥, ⊤), H4) == true
@test alphasat(MVLRCC8Tableau, ⊤, ∨(α, ⊥), H4) == false
@test alphasat(MVLRCC8Tableau, ⊤, ∨(α, α), H4) == false
@test alphasat(MVLRCC8Tableau, ⊤, ∨(α, β), H4) == true
@test alphasat(MVLRCC8Tableau, ⊤, ∨(α, ⊤), H4) == true
@test alphasat(MVLRCC8Tableau, ⊤, ∨(β, ⊥), H4) == false
@test alphasat(MVLRCC8Tableau, ⊤, ∨(β, α), H4) == true
@test alphasat(MVLRCC8Tableau, ⊤, ∨(β, β), H4) == false
@test alphasat(MVLRCC8Tableau, ⊤, ∨(β, ⊤), H4) == true
@test alphasat(MVLRCC8Tableau, ⊤, ∨(⊤, ⊥), H4) == true
@test alphasat(MVLRCC8Tableau, ⊤, ∨(⊤, α), H4) == true
@test alphasat(MVLRCC8Tableau, ⊤, ∨(⊤, β), H4) == true
@test alphasat(MVLRCC8Tableau, ⊤, ∨(⊤, ⊤), H4) == true

@test alphasat(MVLRCC8Tableau, ⊥, ∨(p, ⊥), H4) == true
@test alphasat(MVLRCC8Tableau, ⊥, ∨(p, α), H4) == true
@test alphasat(MVLRCC8Tableau, ⊥, ∨(p, β), H4) == true
@test alphasat(MVLRCC8Tableau, ⊥, ∨(p, ⊤), H4) == true
@test alphasat(MVLRCC8Tableau, α, ∨(p, ⊥), H4) == true
@test alphasat(MVLRCC8Tableau, α, ∨(p, α), H4) == true
@test alphasat(MVLRCC8Tableau, α, ∨(p, β), H4) == true
@test alphasat(MVLRCC8Tableau, α, ∨(p, ⊤), H4) == true
@test alphasat(MVLRCC8Tableau, β, ∨(p, ⊥), H4) == true
@test alphasat(MVLRCC8Tableau, β, ∨(p, α), H4) == true
@test alphasat(MVLRCC8Tableau, β, ∨(p, β), H4) == true
@test alphasat(MVLRCC8Tableau, β, ∨(p, ⊤), H4) == true
@test alphasat(MVLRCC8Tableau, ⊤, ∨(p, ⊥), H4) == true
@test alphasat(MVLRCC8Tableau, ⊤, ∨(p, α), H4) == true
@test alphasat(MVLRCC8Tableau, ⊤, ∨(p, β), H4) == true
@test alphasat(MVLRCC8Tableau, ⊤, ∨(p, ⊤), H4) == true

@test alphasat(MVLRCC8Tableau, ⊥, ∨(⊥, p), H4) == true
@test alphasat(MVLRCC8Tableau, ⊥, ∨(α, p), H4) == true
@test alphasat(MVLRCC8Tableau, ⊥, ∨(β, p), H4) == true
@test alphasat(MVLRCC8Tableau, ⊥, ∨(⊤, p), H4) == true
@test alphasat(MVLRCC8Tableau, α, ∨(⊥, p), H4) == true
@test alphasat(MVLRCC8Tableau, α, ∨(α, p), H4) == true
@test alphasat(MVLRCC8Tableau, α, ∨(β, p), H4) == true
@test alphasat(MVLRCC8Tableau, α, ∨(⊤, p), H4) == true
@test alphasat(MVLRCC8Tableau, β, ∨(⊥, p), H4) == true
@test alphasat(MVLRCC8Tableau, β, ∨(α, p), H4) == true
@test alphasat(MVLRCC8Tableau, β, ∨(β, p), H4) == true
@test alphasat(MVLRCC8Tableau, β, ∨(⊤, p), H4) == true
@test alphasat(MVLRCC8Tableau, ⊤, ∨(⊥, p), H4) == true
@test alphasat(MVLRCC8Tableau, ⊤, ∨(α, p), H4) == true
@test alphasat(MVLRCC8Tableau, ⊤, ∨(β, p), H4) == true
@test alphasat(MVLRCC8Tableau, ⊤, ∨(⊤, p), H4) == true

@test alphasat(MVLRCC8Tableau, ⊥, ∨(p, p), H4)
@test alphasat(MVLRCC8Tableau, α, ∨(p, p), H4)
@test alphasat(MVLRCC8Tableau, β, ∨(p, p), H4)
@test alphasat(MVLRCC8Tableau, ⊤, ∨(p, p), H4)

@test alphasat(MVLRCC8Tableau, ⊥, ∨(p, q), H4)
@test alphasat(MVLRCC8Tableau, α, ∨(p, q), H4)
@test alphasat(MVLRCC8Tableau, β, ∨(p, q), H4)
@test alphasat(MVLRCC8Tableau, ⊤, ∨(p, q), H4)

@test alphasat(MVLRCC8Tableau, ⊥, ∨(q, q), H4)
@test alphasat(MVLRCC8Tableau, α, ∨(q, q), H4)
@test alphasat(MVLRCC8Tableau, β, ∨(q, q), H4)
@test alphasat(MVLRCC8Tableau, ⊤, ∨(q, q), H4)

################################################################################
## (Strong) conjunction ########################################################
################################################################################

@test alphasat(MVLRCC8Tableau, ⊥, ∧(⊥, ⊥), H4) == true
@test alphasat(MVLRCC8Tableau, ⊥, ∧(⊥, α), H4) == true
@test alphasat(MVLRCC8Tableau, ⊥, ∧(⊥, β), H4) == true
@test alphasat(MVLRCC8Tableau, ⊥, ∧(⊥, ⊤), H4) == true
@test alphasat(MVLRCC8Tableau, ⊥, ∧(α, ⊥), H4) == true
@test alphasat(MVLRCC8Tableau, ⊥, ∧(α, α), H4) == true
@test alphasat(MVLRCC8Tableau, ⊥, ∧(α, β), H4) == true
@test alphasat(MVLRCC8Tableau, ⊥, ∧(α, ⊤), H4) == true
@test alphasat(MVLRCC8Tableau, ⊥, ∧(β, ⊥), H4) == true
@test alphasat(MVLRCC8Tableau, ⊥, ∧(β, α), H4) == true
@test alphasat(MVLRCC8Tableau, ⊥, ∧(β, β), H4) == true
@test alphasat(MVLRCC8Tableau, ⊥, ∧(β, ⊤), H4) == true
@test alphasat(MVLRCC8Tableau, ⊥, ∧(⊤, ⊥), H4) == true
@test alphasat(MVLRCC8Tableau, ⊥, ∧(⊤, α), H4) == true
@test alphasat(MVLRCC8Tableau, ⊥, ∧(⊤, β), H4) == true
@test alphasat(MVLRCC8Tableau, ⊥, ∧(⊤, ⊤), H4) == true

@test alphasat(MVLRCC8Tableau, α, ∧(⊥, ⊥), H4) == false
@test alphasat(MVLRCC8Tableau, α, ∧(⊥, α), H4) == false
@test alphasat(MVLRCC8Tableau, α, ∧(⊥, β), H4) == false
@test alphasat(MVLRCC8Tableau, α, ∧(⊥, ⊤), H4) == false
@test alphasat(MVLRCC8Tableau, α, ∧(α, ⊥), H4) == false
@test alphasat(MVLRCC8Tableau, α, ∧(α, α), H4) == true
@test alphasat(MVLRCC8Tableau, α, ∧(α, β), H4) == false
@test alphasat(MVLRCC8Tableau, α, ∧(α, ⊤), H4) == true
@test alphasat(MVLRCC8Tableau, α, ∧(β, ⊥), H4) == false
@test alphasat(MVLRCC8Tableau, α, ∧(β, α), H4) == false
@test alphasat(MVLRCC8Tableau, α, ∧(β, β), H4) == false
@test alphasat(MVLRCC8Tableau, α, ∧(β, ⊤), H4) == false
@test alphasat(MVLRCC8Tableau, α, ∧(⊤, ⊥), H4) == false
@test alphasat(MVLRCC8Tableau, α, ∧(⊤, α), H4) == true
@test alphasat(MVLRCC8Tableau, α, ∧(⊤, β), H4) == false
@test alphasat(MVLRCC8Tableau, α, ∧(⊤, ⊤), H4) == true

@test alphasat(MVLRCC8Tableau, β, ∧(⊥, ⊥), H4) == false
@test alphasat(MVLRCC8Tableau, β, ∧(⊥, α), H4) == false
@test alphasat(MVLRCC8Tableau, β, ∧(⊥, β), H4) == false
@test alphasat(MVLRCC8Tableau, β, ∧(⊥, ⊤), H4) == false
@test alphasat(MVLRCC8Tableau, β, ∧(α, ⊥), H4) == false
@test alphasat(MVLRCC8Tableau, β, ∧(α, α), H4) == false
@test alphasat(MVLRCC8Tableau, β, ∧(α, β), H4) == false
@test alphasat(MVLRCC8Tableau, β, ∧(α, ⊤), H4) == false
@test alphasat(MVLRCC8Tableau, β, ∧(β, ⊥), H4) == false
@test alphasat(MVLRCC8Tableau, β, ∧(β, α), H4) == false
@test alphasat(MVLRCC8Tableau, β, ∧(β, β), H4) == true
@test alphasat(MVLRCC8Tableau, β, ∧(β, ⊤), H4) == true
@test alphasat(MVLRCC8Tableau, β, ∧(⊤, ⊥), H4) == false
@test alphasat(MVLRCC8Tableau, β, ∧(⊤, α), H4) == false
@test alphasat(MVLRCC8Tableau, β, ∧(⊤, β), H4) == true
@test alphasat(MVLRCC8Tableau, β, ∧(⊤, ⊤), H4) == true

@test alphasat(MVLRCC8Tableau, ⊤, ∧(⊥, ⊥), H4) == false
@test alphasat(MVLRCC8Tableau, ⊤, ∧(⊥, α), H4) == false
@test alphasat(MVLRCC8Tableau, ⊤, ∧(⊥, β), H4) == false
@test alphasat(MVLRCC8Tableau, ⊤, ∧(⊥, ⊤), H4) == false
@test alphasat(MVLRCC8Tableau, ⊤, ∧(α, ⊥), H4) == false
@test alphasat(MVLRCC8Tableau, ⊤, ∧(α, α), H4) == false
@test alphasat(MVLRCC8Tableau, ⊤, ∧(α, β), H4) == false
@test alphasat(MVLRCC8Tableau, ⊤, ∧(α, ⊤), H4) == false
@test alphasat(MVLRCC8Tableau, ⊤, ∧(β, ⊥), H4) == false
@test alphasat(MVLRCC8Tableau, ⊤, ∧(β, α), H4) == false
@test alphasat(MVLRCC8Tableau, ⊤, ∧(β, β), H4) == false
@test alphasat(MVLRCC8Tableau, ⊤, ∧(β, ⊤), H4) == false
@test alphasat(MVLRCC8Tableau, ⊤, ∧(⊤, ⊥), H4) == false
@test alphasat(MVLRCC8Tableau, ⊤, ∧(⊤, α), H4) == false
@test alphasat(MVLRCC8Tableau, ⊤, ∧(⊤, β), H4) == false
@test alphasat(MVLRCC8Tableau, ⊤, ∧(⊤, ⊤), H4) == true

@test alphasat(MVLRCC8Tableau, ⊥, ∧(p, ⊥), H4) == true
@test alphasat(MVLRCC8Tableau, ⊥, ∧(p, α), H4) == true
@test alphasat(MVLRCC8Tableau, ⊥, ∧(p, β), H4) == true
@test alphasat(MVLRCC8Tableau, ⊥, ∧(p, ⊤), H4) == true
@test alphasat(MVLRCC8Tableau, α, ∧(p, ⊥), H4) == false
@test alphasat(MVLRCC8Tableau, α, ∧(p, α), H4) == true
@test alphasat(MVLRCC8Tableau, α, ∧(p, β), H4) == false
@test alphasat(MVLRCC8Tableau, α, ∧(p, ⊤), H4) == true
@test alphasat(MVLRCC8Tableau, β, ∧(p, ⊥), H4) == false
@test alphasat(MVLRCC8Tableau, β, ∧(p, α), H4) == false
@test alphasat(MVLRCC8Tableau, β, ∧(p, β), H4) == true
@test alphasat(MVLRCC8Tableau, β, ∧(p, ⊤), H4) == true
@test alphasat(MVLRCC8Tableau, ⊤, ∧(p, ⊥), H4) == false
@test alphasat(MVLRCC8Tableau, ⊤, ∧(p, α), H4) == false
@test alphasat(MVLRCC8Tableau, ⊤, ∧(p, β), H4) == false
@test alphasat(MVLRCC8Tableau, ⊤, ∧(p, ⊤), H4) == true

@test alphasat(MVLRCC8Tableau, ⊥, ∧(⊥, p), H4) == true
@test alphasat(MVLRCC8Tableau, ⊥, ∧(α, p), H4) == true
@test alphasat(MVLRCC8Tableau, ⊥, ∧(β, p), H4) == true
@test alphasat(MVLRCC8Tableau, ⊥, ∧(⊤, p), H4) == true
@test alphasat(MVLRCC8Tableau, α, ∧(⊥, p), H4) == false
@test alphasat(MVLRCC8Tableau, α, ∧(α, p), H4) == true
@test alphasat(MVLRCC8Tableau, α, ∧(β, p), H4) == false
@test alphasat(MVLRCC8Tableau, α, ∧(⊤, p), H4) == true
@test alphasat(MVLRCC8Tableau, β, ∧(⊥, p), H4) == false
@test alphasat(MVLRCC8Tableau, β, ∧(α, p), H4) == false
@test alphasat(MVLRCC8Tableau, β, ∧(β, p), H4) == true
@test alphasat(MVLRCC8Tableau, β, ∧(⊤, p), H4) == true
@test alphasat(MVLRCC8Tableau, ⊤, ∧(⊥, p), H4) == false
@test alphasat(MVLRCC8Tableau, ⊤, ∧(α, p), H4) == false
@test alphasat(MVLRCC8Tableau, ⊤, ∧(β, p), H4) == false
@test alphasat(MVLRCC8Tableau, ⊤, ∧(⊤, p), H4) == true

@test alphasat(MVLRCC8Tableau, ⊥, ∧(p, p), H4)
@test alphasat(MVLRCC8Tableau, α, ∧(p, p), H4)
@test alphasat(MVLRCC8Tableau, β, ∧(p, p), H4)
@test alphasat(MVLRCC8Tableau, ⊤, ∧(p, p), H4)

@test alphasat(MVLRCC8Tableau, ⊥, ∧(p, q), H4)
@test alphasat(MVLRCC8Tableau, α, ∧(p, q), H4)
@test alphasat(MVLRCC8Tableau, β, ∧(p, q), H4)
@test alphasat(MVLRCC8Tableau, ⊤, ∧(p, q), H4)

@test alphasat(MVLRCC8Tableau, ⊥, ∧(q, p), H4)
@test alphasat(MVLRCC8Tableau, α, ∧(q, p), H4)
@test alphasat(MVLRCC8Tableau, β, ∧(q, p), H4)
@test alphasat(MVLRCC8Tableau, ⊤, ∧(q, p), H4)

################################################################################
## Implication #################################################################
################################################################################

@test alphasat(MVLRCC8Tableau, ⊥, →(⊥, ⊥), H4) == true
@test alphasat(MVLRCC8Tableau, ⊥, →(⊥, α), H4) == true
@test alphasat(MVLRCC8Tableau, ⊥, →(⊥, β), H4) == true
@test alphasat(MVLRCC8Tableau, ⊥, →(⊥, ⊤), H4) == true
@test alphasat(MVLRCC8Tableau, ⊥, →(α, ⊥), H4) == true
@test alphasat(MVLRCC8Tableau, ⊥, →(α, α), H4) == true
@test alphasat(MVLRCC8Tableau, ⊥, →(α, β), H4) == true
@test alphasat(MVLRCC8Tableau, ⊥, →(α, ⊤), H4) == true
@test alphasat(MVLRCC8Tableau, ⊥, →(β, ⊥), H4) == true
@test alphasat(MVLRCC8Tableau, ⊥, →(β, α), H4) == true
@test alphasat(MVLRCC8Tableau, ⊥, →(β, β), H4) == true
@test alphasat(MVLRCC8Tableau, ⊥, →(β, ⊤), H4) == true
@test alphasat(MVLRCC8Tableau, ⊥, →(⊤, ⊥), H4) == true
@test alphasat(MVLRCC8Tableau, ⊥, →(⊤, α), H4) == true
@test alphasat(MVLRCC8Tableau, ⊥, →(⊤, β), H4) == true
@test alphasat(MVLRCC8Tableau, ⊥, →(⊤, ⊤), H4) == true

@test alphasat(MVLRCC8Tableau, α, →(⊥, ⊥), H4) == true
@test alphasat(MVLRCC8Tableau, α, →(⊥, α), H4) == true
@test alphasat(MVLRCC8Tableau, α, →(⊥, β), H4) == true
@test alphasat(MVLRCC8Tableau, α, →(⊥, ⊤), H4) == true
@test alphasat(MVLRCC8Tableau, α, →(α, ⊥), H4) == false
@test alphasat(MVLRCC8Tableau, α, →(α, α), H4) == true
@test alphasat(MVLRCC8Tableau, α, →(α, β), H4) == false
@test alphasat(MVLRCC8Tableau, α, →(α, ⊤), H4) == true
@test alphasat(MVLRCC8Tableau, α, →(β, ⊥), H4) == true
@test alphasat(MVLRCC8Tableau, α, →(β, α), H4) == true
@test alphasat(MVLRCC8Tableau, α, →(β, β), H4) == true
@test alphasat(MVLRCC8Tableau, α, →(β, ⊤), H4) == true
@test alphasat(MVLRCC8Tableau, α, →(⊤, ⊥), H4) == false
@test alphasat(MVLRCC8Tableau, α, →(⊤, α), H4) == true
@test alphasat(MVLRCC8Tableau, α, →(⊤, β), H4) == false
@test alphasat(MVLRCC8Tableau, α, →(⊤, ⊤), H4) == true

@test alphasat(MVLRCC8Tableau, β, →(⊥, ⊥), H4) == true
@test alphasat(MVLRCC8Tableau, β, →(⊥, α), H4) == true
@test alphasat(MVLRCC8Tableau, β, →(⊥, β), H4) == true
@test alphasat(MVLRCC8Tableau, β, →(⊥, ⊤), H4) == true
@test alphasat(MVLRCC8Tableau, β, →(α, ⊥), H4) == true
@test alphasat(MVLRCC8Tableau, β, →(α, α), H4) == true
@test alphasat(MVLRCC8Tableau, β, →(α, β), H4) == true
@test alphasat(MVLRCC8Tableau, β, →(α, ⊤), H4) == true
@test alphasat(MVLRCC8Tableau, β, →(β, ⊥), H4) == false
@test alphasat(MVLRCC8Tableau, β, →(β, α), H4) == false
@test alphasat(MVLRCC8Tableau, β, →(β, β), H4) == true
@test alphasat(MVLRCC8Tableau, β, →(β, ⊤), H4) == true
@test alphasat(MVLRCC8Tableau, β, →(⊤, ⊥), H4) == false
@test alphasat(MVLRCC8Tableau, β, →(⊤, α), H4) == false
@test alphasat(MVLRCC8Tableau, β, →(⊤, β), H4) == true
@test alphasat(MVLRCC8Tableau, β, →(⊤, ⊤), H4) == true

@test alphasat(MVLRCC8Tableau, ⊤, →(⊥, ⊥), H4) == true
@test alphasat(MVLRCC8Tableau, ⊤, →(⊥, α), H4) == true
@test alphasat(MVLRCC8Tableau, ⊤, →(⊥, β), H4) == true
@test alphasat(MVLRCC8Tableau, ⊤, →(⊥, ⊤), H4) == true
@test alphasat(MVLRCC8Tableau, ⊤, →(α, ⊥), H4) == false
@test alphasat(MVLRCC8Tableau, ⊤, →(α, α), H4) == true
@test alphasat(MVLRCC8Tableau, ⊤, →(α, β), H4) == false
@test alphasat(MVLRCC8Tableau, ⊤, →(α, ⊤), H4) == true
@test alphasat(MVLRCC8Tableau, ⊤, →(β, ⊥), H4) == false
@test alphasat(MVLRCC8Tableau, ⊤, →(β, α), H4) == false
@test alphasat(MVLRCC8Tableau, ⊤, →(β, β), H4) == true
@test alphasat(MVLRCC8Tableau, ⊤, →(β, ⊤), H4) == true
@test alphasat(MVLRCC8Tableau, ⊤, →(⊤, ⊥), H4) == false
@test alphasat(MVLRCC8Tableau, ⊤, →(⊤, α), H4) == false
@test alphasat(MVLRCC8Tableau, ⊤, →(⊤, β), H4) == false
@test alphasat(MVLRCC8Tableau, ⊤, →(⊤, ⊤), H4) == true

@test alphasat(MVLRCC8Tableau, ⊥, →(p, ⊥), H4) == true
@test alphasat(MVLRCC8Tableau, ⊥, →(p, α), H4) == true
@test alphasat(MVLRCC8Tableau, ⊥, →(p, β), H4) == true
@test alphasat(MVLRCC8Tableau, ⊥, →(p, ⊤), H4) == true
@test alphasat(MVLRCC8Tableau, α, →(p, ⊥), H4) == true
@test alphasat(MVLRCC8Tableau, α, →(p, α), H4) == true
@test alphasat(MVLRCC8Tableau, α, →(p, β), H4) == true
@test alphasat(MVLRCC8Tableau, α, →(p, ⊤), H4) == true
@test alphasat(MVLRCC8Tableau, β, →(p, ⊥), H4) == true
@test alphasat(MVLRCC8Tableau, β, →(p, α), H4) == true
@test alphasat(MVLRCC8Tableau, β, →(p, β), H4) == true
@test alphasat(MVLRCC8Tableau, β, →(p, ⊤), H4) == true
@test alphasat(MVLRCC8Tableau, ⊤, →(p, ⊥), H4) == true
@test alphasat(MVLRCC8Tableau, ⊤, →(p, α), H4) == true
@test alphasat(MVLRCC8Tableau, ⊤, →(p, β), H4) == true
@test alphasat(MVLRCC8Tableau, ⊤, →(p, ⊤), H4) == true

@test alphasat(MVLRCC8Tableau, ⊥, →(⊥, p), H4) == true
@test alphasat(MVLRCC8Tableau, ⊥, →(α, p), H4) == true
@test alphasat(MVLRCC8Tableau, ⊥, →(β, p), H4) == true
@test alphasat(MVLRCC8Tableau, ⊥, →(⊤, p), H4) == true
@test alphasat(MVLRCC8Tableau, α, →(⊥, p), H4) == true
@test alphasat(MVLRCC8Tableau, α, →(α, p), H4) == true
@test alphasat(MVLRCC8Tableau, α, →(β, p), H4) == true
@test alphasat(MVLRCC8Tableau, α, →(⊤, p), H4) == true
@test alphasat(MVLRCC8Tableau, β, →(⊥, p), H4) == true
@test alphasat(MVLRCC8Tableau, β, →(α, p), H4) == true
@test alphasat(MVLRCC8Tableau, β, →(β, p), H4) == true
@test alphasat(MVLRCC8Tableau, β, →(⊤, p), H4) == true
@test alphasat(MVLRCC8Tableau, ⊤, →(⊥, p), H4) == true
@test alphasat(MVLRCC8Tableau, ⊤, →(α, p), H4) == true
@test alphasat(MVLRCC8Tableau, ⊤, →(β, p), H4) == true
@test alphasat(MVLRCC8Tableau, ⊤, →(⊤, p), H4) == true

@test alphasat(MVLRCC8Tableau, ⊥, →(p, p), H4)
@test alphasat(MVLRCC8Tableau, α, →(p, p), H4)
@test alphasat(MVLRCC8Tableau, β, →(p, p), H4)
@test alphasat(MVLRCC8Tableau, ⊤, →(p, p), H4)

@test alphasat(MVLRCC8Tableau, ⊥, →(p, q), H4)
@test alphasat(MVLRCC8Tableau, α, →(p, q), H4)
@test alphasat(MVLRCC8Tableau, β, →(p, q), H4)
@test alphasat(MVLRCC8Tableau, ⊤, →(p, q), H4)

@test alphasat(MVLRCC8Tableau, ⊥, →(q, p), H4)
@test alphasat(MVLRCC8Tableau, α, →(q, p), H4)
@test alphasat(MVLRCC8Tableau, β, →(q, p), H4)
@test alphasat(MVLRCC8Tableau, ⊤, →(q, p), H4)

################################################################################
#### More difficult formulas ###################################################
################################################################################

result = alphasat(MVLRCC8Tableau, ⊤, booleantofuzzy(parseformula(
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
    MVLRCC8Tableau,
    ⊥,
    ∧(diamondLRCC8_Rec_DC(p), boxLRCC8_Rec_DC(→(p, ⊥))),
    H4,
    timeout=timeout
)

if !isnothing(result)
    @test result == true
end

result = alphasat(
    MVLRCC8Tableau,
    α,
    ∧(diamondLRCC8_Rec_DC(p), boxLRCC8_Rec_DC(→(p, ⊥))),
    H4,
    timeout=timeout
)

if !isnothing(result)
    @test result == false
end

result = alphasat(
    MVLRCC8Tableau,
    ⊤,
    ∧(diamondLRCC8_Rec_DC(p), boxLRCC8_Rec_DC(→(p, ⊥))),
    H4,
    timeout=timeout
)

if !isnothing(result)
    @test result == false
end

result = alphasat(
    MVLRCC8Tableau,
    ⊥,
    ∧(diamondLRCC8_Rec_EC(p), boxLRCC8_Rec_EC(→(p, ⊥))),
    H4,
    timeout=timeout
)

if !isnothing(result)
    @test result == true
end

result = alphasat(
    MVLRCC8Tableau,
    α,
    ∧(diamondLRCC8_Rec_EC(p), boxLRCC8_Rec_EC(→(p, ⊥))),
    H4,
    timeout=timeout
)

if !isnothing(result)
    @test result == false
end

result = alphasat(
    MVLRCC8Tableau,
    ⊤,
    ∧(diamondLRCC8_Rec_EC(p), boxLRCC8_Rec_EC(→(p, ⊥))),
    H4,
    timeout=timeout
)

if !isnothing(result)
    @test result == false
end

result = alphasat(
    MVLRCC8Tableau,
    ⊥,
    ∧(diamondLRCC8_Rec_PO(p), boxLRCC8_Rec_PO(→(p, ⊥))),
    H4,
    timeout=timeout
)

if !isnothing(result)
    @test result == true
end

result = alphasat(
    MVLRCC8Tableau,
    α,
    ∧(diamondLRCC8_Rec_PO(p), boxLRCC8_Rec_PO(→(p, ⊥))),
    H4,
    timeout=timeout
)

if !isnothing(result)
    @test result == false
end

result = alphasat(
    MVLRCC8Tableau,
    ⊤,
    ∧(diamondLRCC8_Rec_PO(p), boxLRCC8_Rec_PO(→(p, ⊥))),
    H4,
    timeout=timeout
)

if !isnothing(result)
    @test result == false
end

result = alphasat(
    MVLRCC8Tableau,
    ⊥,
    ∧(diamondLRCC8_Rec_TPP(p), boxLRCC8_Rec_TPP(→(p, ⊥))),
    H4,
    timeout=timeout
)

if !isnothing(result)
    @test result == true
end

result = alphasat(
    MVLRCC8Tableau,
    α,
    ∧(diamondLRCC8_Rec_TPP(p), boxLRCC8_Rec_TPP(→(p, ⊥))),
    H4,
    timeout=timeout
)

if !isnothing(result)
    @test result == false
end

result = alphasat(
    MVLRCC8Tableau,
    ⊤,
    ∧(diamondLRCC8_Rec_TPP(p), boxLRCC8_Rec_TPP(→(p, ⊥))),
    H4,
    timeout=timeout
)

if !isnothing(result)
    @test result == false
end

result = alphasat(
    MVLRCC8Tableau,
    ⊥,
    ∧(diamondLRCC8_Rec_TPPi(p), boxLRCC8_Rec_TPPi(→(p, ⊥))),
    H4,
    timeout=timeout
)

if !isnothing(result)
    @test result == true
end

result = alphasat(
    MVLRCC8Tableau,
    α,
    ∧(diamondLRCC8_Rec_TPPi(p), boxLRCC8_Rec_TPPi(→(p, ⊥))),
    H4,
    timeout=timeout
)

if !isnothing(result)
    @test result == false
end

result = alphasat(
    MVLRCC8Tableau,
    ⊤,
    ∧(diamondLRCC8_Rec_TPPi(p), boxLRCC8_Rec_TPPi(→(p, ⊥))),
    H4,
    timeout=timeout
)

if !isnothing(result)
    @test result == false
end

result = alphasat(
    MVLRCC8Tableau,
    ⊥,
    ∧(diamondLRCC8_Rec_NTPP(p), boxLRCC8_Rec_NTPP(→(p, ⊥))),
    H4,
    timeout=timeout
)

if !isnothing(result)
    @test result == true
end

result = alphasat(
    MVLRCC8Tableau,
    α,
    ∧(diamondLRCC8_Rec_NTPP(p), boxLRCC8_Rec_NTPP(→(p, ⊥))),
    H4,
    timeout=timeout
)

if !isnothing(result)
    @test result == false
end

result = alphasat(
    MVLRCC8Tableau,
    ⊤,
    ∧(diamondLRCC8_Rec_NTPP(p), boxLRCC8_Rec_NTPP(→(p, ⊥))),
    H4,
    timeout=timeout
)

if !isnothing(result)
    @test result == false
end

result = alphasat(
    MVLRCC8Tableau,
    ⊥,
    ∧(diamondLRCC8_Rec_NTPPi(p), boxLRCC8_Rec_NTPPi(→(p, ⊥))),
    H4,
    timeout=timeout
)

if !isnothing(result)
    @test result == true
end

result = alphasat(
    MVLRCC8Tableau,
    α,
    ∧(diamondLRCC8_Rec_NTPPi(p), boxLRCC8_Rec_NTPPi(→(p, ⊥))),
    H4,
    timeout=timeout
)

if !isnothing(result)
    @test result == false
end

result = alphasat(
    MVLRCC8Tableau,
    ⊤,
    ∧(diamondLRCC8_Rec_NTPPi(p), boxLRCC8_Rec_NTPPi(→(p, ⊥))),
    H4,
    timeout=timeout
)

if !isnothing(result)
    @test result == false
end
