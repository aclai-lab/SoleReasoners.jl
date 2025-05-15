################################################################################
#### H4 ########################################################################
################################################################################

using SoleLogics.ManyValuedLogics: H4
using SoleLogics.ManyValuedLogics: α, β

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

@test alphasat(MVHSTableau, ⊥, parseformula("p"), H4) == true
@test alphasat(MVHSTableau, α, parseformula("p"), H4) == true
@test alphasat(MVHSTableau, β, parseformula("p"), H4) == true
@test alphasat(MVHSTableau, ⊤, parseformula("p"), H4) == true

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

@test alphasat(MVHSTableau, ⊥, ∨(parseformula("p"), ⊥), H4) == true
@test alphasat(MVHSTableau, ⊥, ∨(parseformula("p"), α), H4) == true
@test alphasat(MVHSTableau, ⊥, ∨(parseformula("p"), β), H4) == true
@test alphasat(MVHSTableau, ⊥, ∨(parseformula("p"), ⊤), H4) == true
@test alphasat(MVHSTableau, α, ∨(parseformula("p"), ⊥), H4) == true
@test alphasat(MVHSTableau, α, ∨(parseformula("p"), α), H4) == true
@test alphasat(MVHSTableau, α, ∨(parseformula("p"), β), H4) == true
@test alphasat(MVHSTableau, α, ∨(parseformula("p"), ⊤), H4) == true
@test alphasat(MVHSTableau, β, ∨(parseformula("p"), ⊥), H4) == true
@test alphasat(MVHSTableau, β, ∨(parseformula("p"), α), H4) == true
@test alphasat(MVHSTableau, β, ∨(parseformula("p"), β), H4) == true
@test alphasat(MVHSTableau, β, ∨(parseformula("p"), ⊤), H4) == true
@test alphasat(MVHSTableau, ⊤, ∨(parseformula("p"), ⊥), H4) == true
@test alphasat(MVHSTableau, ⊤, ∨(parseformula("p"), α), H4) == true
@test alphasat(MVHSTableau, ⊤, ∨(parseformula("p"), β), H4) == true
@test alphasat(MVHSTableau, ⊤, ∨(parseformula("p"), ⊤), H4) == true

@test alphasat(MVHSTableau, ⊥, ∨(⊥, parseformula("p")), H4) == true
@test alphasat(MVHSTableau, ⊥, ∨(α, parseformula("p")), H4) == true
@test alphasat(MVHSTableau, ⊥, ∨(β, parseformula("p")), H4) == true
@test alphasat(MVHSTableau, ⊥, ∨(⊤, parseformula("p")), H4) == true
@test alphasat(MVHSTableau, α, ∨(⊥, parseformula("p")), H4) == true
@test alphasat(MVHSTableau, α, ∨(α, parseformula("p")), H4) == true
@test alphasat(MVHSTableau, α, ∨(β, parseformula("p")), H4) == true
@test alphasat(MVHSTableau, α, ∨(⊤, parseformula("p")), H4) == true
@test alphasat(MVHSTableau, β, ∨(⊥, parseformula("p")), H4) == true
@test alphasat(MVHSTableau, β, ∨(α, parseformula("p")), H4) == true
@test alphasat(MVHSTableau, β, ∨(β, parseformula("p")), H4) == true
@test alphasat(MVHSTableau, β, ∨(⊤, parseformula("p")), H4) == true
@test alphasat(MVHSTableau, ⊤, ∨(⊥, parseformula("p")), H4) == true
@test alphasat(MVHSTableau, ⊤, ∨(α, parseformula("p")), H4) == true
@test alphasat(MVHSTableau, ⊤, ∨(β, parseformula("p")), H4) == true
@test alphasat(MVHSTableau, ⊤, ∨(⊤, parseformula("p")), H4) == true

@test alphasat(MVHSTableau, ⊥, ∨(parseformula("p"), parseformula("p")), H4)
@test alphasat(MVHSTableau, α, ∨(parseformula("p"), parseformula("p")), H4)
@test alphasat(MVHSTableau, β, ∨(parseformula("p"), parseformula("p")), H4)
@test alphasat(MVHSTableau, ⊤, ∨(parseformula("p"), parseformula("p")), H4)

@test alphasat(MVHSTableau, ⊥, ∨(parseformula("p"), parseformula("q")), H4)
@test alphasat(MVHSTableau, α, ∨(parseformula("p"), parseformula("q")), H4)
@test alphasat(MVHSTableau, β, ∨(parseformula("p"), parseformula("q")), H4)
@test alphasat(MVHSTableau, ⊤, ∨(parseformula("p"), parseformula("q")), H4)

@test alphasat(MVHSTableau, ⊥, ∨(parseformula("q"), parseformula("q")), H4)
@test alphasat(MVHSTableau, α, ∨(parseformula("q"), parseformula("q")), H4)
@test alphasat(MVHSTableau, β, ∨(parseformula("q"), parseformula("q")), H4)
@test alphasat(MVHSTableau, ⊤, ∨(parseformula("q"), parseformula("q")), H4)

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

@test alphasat(MVHSTableau, ⊥, ∧(parseformula("p"), ⊥), H4) == true
@test alphasat(MVHSTableau, ⊥, ∧(parseformula("p"), α), H4) == true
@test alphasat(MVHSTableau, ⊥, ∧(parseformula("p"), β), H4) == true
@test alphasat(MVHSTableau, ⊥, ∧(parseformula("p"), ⊤), H4) == true
@test alphasat(MVHSTableau, α, ∧(parseformula("p"), ⊥), H4) == false
@test alphasat(MVHSTableau, α, ∧(parseformula("p"), α), H4) == true
@test alphasat(MVHSTableau, α, ∧(parseformula("p"), β), H4) == false
@test alphasat(MVHSTableau, α, ∧(parseformula("p"), ⊤), H4) == true
@test alphasat(MVHSTableau, β, ∧(parseformula("p"), ⊥), H4) == false
@test alphasat(MVHSTableau, β, ∧(parseformula("p"), α), H4) == false
@test alphasat(MVHSTableau, β, ∧(parseformula("p"), β), H4) == true
@test alphasat(MVHSTableau, β, ∧(parseformula("p"), ⊤), H4) == true
@test alphasat(MVHSTableau, ⊤, ∧(parseformula("p"), ⊥), H4) == false
@test alphasat(MVHSTableau, ⊤, ∧(parseformula("p"), α), H4) == false
@test alphasat(MVHSTableau, ⊤, ∧(parseformula("p"), β), H4) == false
@test alphasat(MVHSTableau, ⊤, ∧(parseformula("p"), ⊤), H4) == true

@test alphasat(MVHSTableau, ⊥, ∧(⊥, parseformula("p")), H4) == true
@test alphasat(MVHSTableau, ⊥, ∧(α, parseformula("p")), H4) == true
@test alphasat(MVHSTableau, ⊥, ∧(β, parseformula("p")), H4) == true
@test alphasat(MVHSTableau, ⊥, ∧(⊤, parseformula("p")), H4) == true
@test alphasat(MVHSTableau, α, ∧(⊥, parseformula("p")), H4) == false
@test alphasat(MVHSTableau, α, ∧(α, parseformula("p")), H4) == true
@test alphasat(MVHSTableau, α, ∧(β, parseformula("p")), H4) == false
@test alphasat(MVHSTableau, α, ∧(⊤, parseformula("p")), H4) == true
@test alphasat(MVHSTableau, β, ∧(⊥, parseformula("p")), H4) == false
@test alphasat(MVHSTableau, β, ∧(α, parseformula("p")), H4) == false
@test alphasat(MVHSTableau, β, ∧(β, parseformula("p")), H4) == true
@test alphasat(MVHSTableau, β, ∧(⊤, parseformula("p")), H4) == true
@test alphasat(MVHSTableau, ⊤, ∧(⊥, parseformula("p")), H4) == false
@test alphasat(MVHSTableau, ⊤, ∧(α, parseformula("p")), H4) == false
@test alphasat(MVHSTableau, ⊤, ∧(β, parseformula("p")), H4) == false
@test alphasat(MVHSTableau, ⊤, ∧(⊤, parseformula("p")), H4) == true

@test alphasat(MVHSTableau, ⊥, ∧(parseformula("p"), parseformula("p")), H4)
@test alphasat(MVHSTableau, α, ∧(parseformula("p"), parseformula("p")), H4)
@test alphasat(MVHSTableau, β, ∧(parseformula("p"), parseformula("p")), H4)
@test alphasat(MVHSTableau, ⊤, ∧(parseformula("p"), parseformula("p")), H4)

@test alphasat(MVHSTableau, ⊥, ∧(parseformula("p"), parseformula("q")), H4)
@test alphasat(MVHSTableau, α, ∧(parseformula("p"), parseformula("q")), H4)
@test alphasat(MVHSTableau, β, ∧(parseformula("p"), parseformula("q")), H4)
@test alphasat(MVHSTableau, ⊤, ∧(parseformula("p"), parseformula("q")), H4)

@test alphasat(MVHSTableau, ⊥, ∧(parseformula("q"), parseformula("p")), H4)
@test alphasat(MVHSTableau, α, ∧(parseformula("q"), parseformula("p")), H4)
@test alphasat(MVHSTableau, β, ∧(parseformula("q"), parseformula("p")), H4)
@test alphasat(MVHSTableau, ⊤, ∧(parseformula("q"), parseformula("p")), H4)

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

@test alphasat(MVHSTableau, ⊥, →(parseformula("p"), ⊥), H4) == true
@test alphasat(MVHSTableau, ⊥, →(parseformula("p"), α), H4) == true
@test alphasat(MVHSTableau, ⊥, →(parseformula("p"), β), H4) == true
@test alphasat(MVHSTableau, ⊥, →(parseformula("p"), ⊤), H4) == true
@test alphasat(MVHSTableau, α, →(parseformula("p"), ⊥), H4) == true
@test alphasat(MVHSTableau, α, →(parseformula("p"), α), H4) == true
@test alphasat(MVHSTableau, α, →(parseformula("p"), β), H4) == true
@test alphasat(MVHSTableau, α, →(parseformula("p"), ⊤), H4) == true
@test alphasat(MVHSTableau, β, →(parseformula("p"), ⊥), H4) == true
@test alphasat(MVHSTableau, β, →(parseformula("p"), α), H4) == true
@test alphasat(MVHSTableau, β, →(parseformula("p"), β), H4) == true
@test alphasat(MVHSTableau, β, →(parseformula("p"), ⊤), H4) == true
@test alphasat(MVHSTableau, ⊤, →(parseformula("p"), ⊥), H4) == true
@test alphasat(MVHSTableau, ⊤, →(parseformula("p"), α), H4) == true
@test alphasat(MVHSTableau, ⊤, →(parseformula("p"), β), H4) == true
@test alphasat(MVHSTableau, ⊤, →(parseformula("p"), ⊤), H4) == true

@test alphasat(MVHSTableau, ⊥, →(⊥, parseformula("p")), H4) == true
@test alphasat(MVHSTableau, ⊥, →(α, parseformula("p")), H4) == true
@test alphasat(MVHSTableau, ⊥, →(β, parseformula("p")), H4) == true
@test alphasat(MVHSTableau, ⊥, →(⊤, parseformula("p")), H4) == true
@test alphasat(MVHSTableau, α, →(⊥, parseformula("p")), H4) == true
@test alphasat(MVHSTableau, α, →(α, parseformula("p")), H4) == true
@test alphasat(MVHSTableau, α, →(β, parseformula("p")), H4) == true
@test alphasat(MVHSTableau, α, →(⊤, parseformula("p")), H4) == true
@test alphasat(MVHSTableau, β, →(⊥, parseformula("p")), H4) == true
@test alphasat(MVHSTableau, β, →(α, parseformula("p")), H4) == true
@test alphasat(MVHSTableau, β, →(β, parseformula("p")), H4) == true
@test alphasat(MVHSTableau, β, →(⊤, parseformula("p")), H4) == true
@test alphasat(MVHSTableau, ⊤, →(⊥, parseformula("p")), H4) == true
@test alphasat(MVHSTableau, ⊤, →(α, parseformula("p")), H4) == true
@test alphasat(MVHSTableau, ⊤, →(β, parseformula("p")), H4) == true
@test alphasat(MVHSTableau, ⊤, →(⊤, parseformula("p")), H4) == true

@test alphasat(MVHSTableau, ⊥, →(parseformula("p"), parseformula("p")), H4)
@test alphasat(MVHSTableau, α, →(parseformula("p"), parseformula("p")), H4)
@test alphasat(MVHSTableau, β, →(parseformula("p"), parseformula("p")), H4)
@test alphasat(MVHSTableau, ⊤, →(parseformula("p"), parseformula("p")), H4)

@test alphasat(MVHSTableau, ⊥, →(parseformula("p"), parseformula("q")), H4)
@test alphasat(MVHSTableau, α, →(parseformula("p"), parseformula("q")), H4)
@test alphasat(MVHSTableau, β, →(parseformula("p"), parseformula("q")), H4)
@test alphasat(MVHSTableau, ⊤, →(parseformula("p"), parseformula("q")), H4)

@test alphasat(MVHSTableau, ⊥, →(parseformula("q"), parseformula("p")), H4)
@test alphasat(MVHSTableau, α, →(parseformula("q"), parseformula("p")), H4)
@test alphasat(MVHSTableau, β, →(parseformula("q"), parseformula("p")), H4)
@test alphasat(MVHSTableau, ⊤, →(parseformula("q"), parseformula("p")), H4)

################################################################################
#### More difficult formulas ###################################################
################################################################################

@test alphasat(MVHSTableau, ⊤, booleantofuzzy(parseformula(
    "(x∨y∨z)∧(x∨y∨¬z)∧(x∨¬y∨z)∧(x∨¬y∨¬z)∧" *
    "(¬x∨y∨z)∧(¬x∨y∨¬z)∧(¬x∨¬y∨z)∧(¬x∨¬y∨¬z)"
)), H4) == false
