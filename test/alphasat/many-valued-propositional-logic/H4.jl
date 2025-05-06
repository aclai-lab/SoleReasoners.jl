using SoleReasoners: MVLTLFPTableau

################################################################################
#### H4 ########################################################################
################################################################################

using SoleLogics.ManyValuedLogics: H4
using SoleLogics.ManyValuedLogics: α, β

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

@test alphasat(MVLTLFPTableau, ⊥, parseformula("p"), H4) == true
@test alphasat(MVLTLFPTableau, α, parseformula("p"), H4) == true
@test alphasat(MVLTLFPTableau, β, parseformula("p"), H4) == true
@test alphasat(MVLTLFPTableau, ⊤, parseformula("p"), H4) == true

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

@test alphasat(MVLTLFPTableau, ⊥, ∨(parseformula("p"), ⊥), H4) == true
@test alphasat(MVLTLFPTableau, ⊥, ∨(parseformula("p"), α), H4) == true
@test alphasat(MVLTLFPTableau, ⊥, ∨(parseformula("p"), β), H4) == true
@test alphasat(MVLTLFPTableau, ⊥, ∨(parseformula("p"), ⊤), H4) == true
@test alphasat(MVLTLFPTableau, α, ∨(parseformula("p"), ⊥), H4) == true
@test alphasat(MVLTLFPTableau, α, ∨(parseformula("p"), α), H4) == true
@test alphasat(MVLTLFPTableau, α, ∨(parseformula("p"), β), H4) == true
@test alphasat(MVLTLFPTableau, α, ∨(parseformula("p"), ⊤), H4) == true
@test alphasat(MVLTLFPTableau, β, ∨(parseformula("p"), ⊥), H4) == true
@test alphasat(MVLTLFPTableau, β, ∨(parseformula("p"), α), H4) == true
@test alphasat(MVLTLFPTableau, β, ∨(parseformula("p"), β), H4) == true
@test alphasat(MVLTLFPTableau, β, ∨(parseformula("p"), ⊤), H4) == true
@test alphasat(MVLTLFPTableau, ⊤, ∨(parseformula("p"), ⊥), H4) == true
@test alphasat(MVLTLFPTableau, ⊤, ∨(parseformula("p"), α), H4) == true
@test alphasat(MVLTLFPTableau, ⊤, ∨(parseformula("p"), β), H4) == true
@test alphasat(MVLTLFPTableau, ⊤, ∨(parseformula("p"), ⊤), H4) == true

@test alphasat(MVLTLFPTableau, ⊥, ∨(⊥, parseformula("p")), H4) == true
@test alphasat(MVLTLFPTableau, ⊥, ∨(α, parseformula("p")), H4) == true
@test alphasat(MVLTLFPTableau, ⊥, ∨(β, parseformula("p")), H4) == true
@test alphasat(MVLTLFPTableau, ⊥, ∨(⊤, parseformula("p")), H4) == true
@test alphasat(MVLTLFPTableau, α, ∨(⊥, parseformula("p")), H4) == true
@test alphasat(MVLTLFPTableau, α, ∨(α, parseformula("p")), H4) == true
@test alphasat(MVLTLFPTableau, α, ∨(β, parseformula("p")), H4) == true
@test alphasat(MVLTLFPTableau, α, ∨(⊤, parseformula("p")), H4) == true
@test alphasat(MVLTLFPTableau, β, ∨(⊥, parseformula("p")), H4) == true
@test alphasat(MVLTLFPTableau, β, ∨(α, parseformula("p")), H4) == true
@test alphasat(MVLTLFPTableau, β, ∨(β, parseformula("p")), H4) == true
@test alphasat(MVLTLFPTableau, β, ∨(⊤, parseformula("p")), H4) == true
@test alphasat(MVLTLFPTableau, ⊤, ∨(⊥, parseformula("p")), H4) == true
@test alphasat(MVLTLFPTableau, ⊤, ∨(α, parseformula("p")), H4) == true
@test alphasat(MVLTLFPTableau, ⊤, ∨(β, parseformula("p")), H4) == true
@test alphasat(MVLTLFPTableau, ⊤, ∨(⊤, parseformula("p")), H4) == true

@test alphasat(MVLTLFPTableau, ⊥, ∨(parseformula("p"), parseformula("p")), H4)
@test alphasat(MVLTLFPTableau, α, ∨(parseformula("p"), parseformula("p")), H4)
@test alphasat(MVLTLFPTableau, β, ∨(parseformula("p"), parseformula("p")), H4)
@test alphasat(MVLTLFPTableau, ⊤, ∨(parseformula("p"), parseformula("p")), H4)

@test alphasat(MVLTLFPTableau, ⊥, ∨(parseformula("p"), parseformula("q")), H4)
@test alphasat(MVLTLFPTableau, α, ∨(parseformula("p"), parseformula("q")), H4)
@test alphasat(MVLTLFPTableau, β, ∨(parseformula("p"), parseformula("q")), H4)
@test alphasat(MVLTLFPTableau, ⊤, ∨(parseformula("p"), parseformula("q")), H4)

@test alphasat(MVLTLFPTableau, ⊥, ∨(parseformula("q"), parseformula("q")), H4)
@test alphasat(MVLTLFPTableau, α, ∨(parseformula("q"), parseformula("q")), H4)
@test alphasat(MVLTLFPTableau, β, ∨(parseformula("q"), parseformula("q")), H4)
@test alphasat(MVLTLFPTableau, ⊤, ∨(parseformula("q"), parseformula("q")), H4)

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

@test alphasat(MVLTLFPTableau, ⊥, ∧(parseformula("p"), ⊥), H4) == true
@test alphasat(MVLTLFPTableau, ⊥, ∧(parseformula("p"), α), H4) == true
@test alphasat(MVLTLFPTableau, ⊥, ∧(parseformula("p"), β), H4) == true
@test alphasat(MVLTLFPTableau, ⊥, ∧(parseformula("p"), ⊤), H4) == true
@test alphasat(MVLTLFPTableau, α, ∧(parseformula("p"), ⊥), H4) == false
@test alphasat(MVLTLFPTableau, α, ∧(parseformula("p"), α), H4) == true
@test alphasat(MVLTLFPTableau, α, ∧(parseformula("p"), β), H4) == false
@test alphasat(MVLTLFPTableau, α, ∧(parseformula("p"), ⊤), H4) == true
@test alphasat(MVLTLFPTableau, β, ∧(parseformula("p"), ⊥), H4) == false
@test alphasat(MVLTLFPTableau, β, ∧(parseformula("p"), α), H4) == false
@test alphasat(MVLTLFPTableau, β, ∧(parseformula("p"), β), H4) == true
@test alphasat(MVLTLFPTableau, β, ∧(parseformula("p"), ⊤), H4) == true
@test alphasat(MVLTLFPTableau, ⊤, ∧(parseformula("p"), ⊥), H4) == false
@test alphasat(MVLTLFPTableau, ⊤, ∧(parseformula("p"), α), H4) == false
@test alphasat(MVLTLFPTableau, ⊤, ∧(parseformula("p"), β), H4) == false
@test alphasat(MVLTLFPTableau, ⊤, ∧(parseformula("p"), ⊤), H4) == true

@test alphasat(MVLTLFPTableau, ⊥, ∧(⊥, parseformula("p")), H4) == true
@test alphasat(MVLTLFPTableau, ⊥, ∧(α, parseformula("p")), H4) == true
@test alphasat(MVLTLFPTableau, ⊥, ∧(β, parseformula("p")), H4) == true
@test alphasat(MVLTLFPTableau, ⊥, ∧(⊤, parseformula("p")), H4) == true
@test alphasat(MVLTLFPTableau, α, ∧(⊥, parseformula("p")), H4) == false
@test alphasat(MVLTLFPTableau, α, ∧(α, parseformula("p")), H4) == true
@test alphasat(MVLTLFPTableau, α, ∧(β, parseformula("p")), H4) == false
@test alphasat(MVLTLFPTableau, α, ∧(⊤, parseformula("p")), H4) == true
@test alphasat(MVLTLFPTableau, β, ∧(⊥, parseformula("p")), H4) == false
@test alphasat(MVLTLFPTableau, β, ∧(α, parseformula("p")), H4) == false
@test alphasat(MVLTLFPTableau, β, ∧(β, parseformula("p")), H4) == true
@test alphasat(MVLTLFPTableau, β, ∧(⊤, parseformula("p")), H4) == true
@test alphasat(MVLTLFPTableau, ⊤, ∧(⊥, parseformula("p")), H4) == false
@test alphasat(MVLTLFPTableau, ⊤, ∧(α, parseformula("p")), H4) == false
@test alphasat(MVLTLFPTableau, ⊤, ∧(β, parseformula("p")), H4) == false
@test alphasat(MVLTLFPTableau, ⊤, ∧(⊤, parseformula("p")), H4) == true

@test alphasat(MVLTLFPTableau, ⊥, ∧(parseformula("p"), parseformula("p")), H4)
@test alphasat(MVLTLFPTableau, α, ∧(parseformula("p"), parseformula("p")), H4)
@test alphasat(MVLTLFPTableau, β, ∧(parseformula("p"), parseformula("p")), H4)
@test alphasat(MVLTLFPTableau, ⊤, ∧(parseformula("p"), parseformula("p")), H4)

@test alphasat(MVLTLFPTableau, ⊥, ∧(parseformula("p"), parseformula("q")), H4)
@test alphasat(MVLTLFPTableau, α, ∧(parseformula("p"), parseformula("q")), H4)
@test alphasat(MVLTLFPTableau, β, ∧(parseformula("p"), parseformula("q")), H4)
@test alphasat(MVLTLFPTableau, ⊤, ∧(parseformula("p"), parseformula("q")), H4)

@test alphasat(MVLTLFPTableau, ⊥, ∧(parseformula("q"), parseformula("p")), H4)
@test alphasat(MVLTLFPTableau, α, ∧(parseformula("q"), parseformula("p")), H4)
@test alphasat(MVLTLFPTableau, β, ∧(parseformula("q"), parseformula("p")), H4)
@test alphasat(MVLTLFPTableau, ⊤, ∧(parseformula("q"), parseformula("p")), H4)

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

@test alphasat(MVLTLFPTableau, ⊥, →(parseformula("p"), ⊥), H4) == true
@test alphasat(MVLTLFPTableau, ⊥, →(parseformula("p"), α), H4) == true
@test alphasat(MVLTLFPTableau, ⊥, →(parseformula("p"), β), H4) == true
@test alphasat(MVLTLFPTableau, ⊥, →(parseformula("p"), ⊤), H4) == true
@test alphasat(MVLTLFPTableau, α, →(parseformula("p"), ⊥), H4) == true
@test alphasat(MVLTLFPTableau, α, →(parseformula("p"), α), H4) == true
@test alphasat(MVLTLFPTableau, α, →(parseformula("p"), β), H4) == true
@test alphasat(MVLTLFPTableau, α, →(parseformula("p"), ⊤), H4) == true
@test alphasat(MVLTLFPTableau, β, →(parseformula("p"), ⊥), H4) == true
@test alphasat(MVLTLFPTableau, β, →(parseformula("p"), α), H4) == true
@test alphasat(MVLTLFPTableau, β, →(parseformula("p"), β), H4) == true
@test alphasat(MVLTLFPTableau, β, →(parseformula("p"), ⊤), H4) == true
@test alphasat(MVLTLFPTableau, ⊤, →(parseformula("p"), ⊥), H4) == true
@test alphasat(MVLTLFPTableau, ⊤, →(parseformula("p"), α), H4) == true
@test alphasat(MVLTLFPTableau, ⊤, →(parseformula("p"), β), H4) == true
@test alphasat(MVLTLFPTableau, ⊤, →(parseformula("p"), ⊤), H4) == true

@test alphasat(MVLTLFPTableau, ⊥, →(⊥, parseformula("p")), H4) == true
@test alphasat(MVLTLFPTableau, ⊥, →(α, parseformula("p")), H4) == true
@test alphasat(MVLTLFPTableau, ⊥, →(β, parseformula("p")), H4) == true
@test alphasat(MVLTLFPTableau, ⊥, →(⊤, parseformula("p")), H4) == true
@test alphasat(MVLTLFPTableau, α, →(⊥, parseformula("p")), H4) == true
@test alphasat(MVLTLFPTableau, α, →(α, parseformula("p")), H4) == true
@test alphasat(MVLTLFPTableau, α, →(β, parseformula("p")), H4) == true
@test alphasat(MVLTLFPTableau, α, →(⊤, parseformula("p")), H4) == true
@test alphasat(MVLTLFPTableau, β, →(⊥, parseformula("p")), H4) == true
@test alphasat(MVLTLFPTableau, β, →(α, parseformula("p")), H4) == true
@test alphasat(MVLTLFPTableau, β, →(β, parseformula("p")), H4) == true
@test alphasat(MVLTLFPTableau, β, →(⊤, parseformula("p")), H4) == true
@test alphasat(MVLTLFPTableau, ⊤, →(⊥, parseformula("p")), H4) == true
@test alphasat(MVLTLFPTableau, ⊤, →(α, parseformula("p")), H4) == true
@test alphasat(MVLTLFPTableau, ⊤, →(β, parseformula("p")), H4) == true
@test alphasat(MVLTLFPTableau, ⊤, →(⊤, parseformula("p")), H4) == true

@test alphasat(MVLTLFPTableau, ⊥, →(parseformula("p"), parseformula("p")), H4)
@test alphasat(MVLTLFPTableau, α, →(parseformula("p"), parseformula("p")), H4)
@test alphasat(MVLTLFPTableau, β, →(parseformula("p"), parseformula("p")), H4)
@test alphasat(MVLTLFPTableau, ⊤, →(parseformula("p"), parseformula("p")), H4)

@test alphasat(MVLTLFPTableau, ⊥, →(parseformula("p"), parseformula("q")), H4)
@test alphasat(MVLTLFPTableau, α, →(parseformula("p"), parseformula("q")), H4)
@test alphasat(MVLTLFPTableau, β, →(parseformula("p"), parseformula("q")), H4)
@test alphasat(MVLTLFPTableau, ⊤, →(parseformula("p"), parseformula("q")), H4)

@test alphasat(MVLTLFPTableau, ⊥, →(parseformula("q"), parseformula("p")), H4)
@test alphasat(MVLTLFPTableau, α, →(parseformula("q"), parseformula("p")), H4)
@test alphasat(MVLTLFPTableau, β, →(parseformula("q"), parseformula("p")), H4)
@test alphasat(MVLTLFPTableau, ⊤, →(parseformula("q"), parseformula("p")), H4)

################################################################################
#### More difficult formulas ###################################################
################################################################################

@test alphasat(MVLTLFPTableau, ⊤, booleantofuzzy(parseformula(
    "(x∨y∨z)∧(x∨y∨¬z)∧(x∨¬y∨z)∧(x∨¬y∨¬z)∧" *
    "(¬x∨y∨z)∧(¬x∨y∨¬z)∧(¬x∨¬y∨z)∧(¬x∨¬y∨¬z)"
)), H4) == false
