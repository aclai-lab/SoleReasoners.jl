################################################################################
#### G4 ########################################################################
################################################################################

using SoleLogics.ManyValuedLogics: G4
using SoleLogics.ManyValuedLogics: α, β

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

@test alphasat(MVHSTableau, ⊥, parseformula("p"), G4) == true
@test alphasat(MVHSTableau, α, parseformula("p"), G4) == true
@test alphasat(MVHSTableau, β, parseformula("p"), G4) == true
@test alphasat(MVHSTableau, ⊤, parseformula("p"), G4) == true

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

@test alphasat(MVHSTableau, ⊥, ∨(parseformula("p"), ⊥), G4) == true
@test alphasat(MVHSTableau, ⊥, ∨(parseformula("p"), α), G4) == true
@test alphasat(MVHSTableau, ⊥, ∨(parseformula("p"), β), G4) == true
@test alphasat(MVHSTableau, ⊥, ∨(parseformula("p"), ⊤), G4) == true
@test alphasat(MVHSTableau, α, ∨(parseformula("p"), ⊥), G4) == true
@test alphasat(MVHSTableau, α, ∨(parseformula("p"), α), G4) == true
@test alphasat(MVHSTableau, α, ∨(parseformula("p"), β), G4) == true
@test alphasat(MVHSTableau, α, ∨(parseformula("p"), ⊤), G4) == true
@test alphasat(MVHSTableau, β, ∨(parseformula("p"), ⊥), G4) == true
@test alphasat(MVHSTableau, β, ∨(parseformula("p"), α), G4) == true
@test alphasat(MVHSTableau, β, ∨(parseformula("p"), β), G4) == true
@test alphasat(MVHSTableau, β, ∨(parseformula("p"), ⊤), G4) == true
@test alphasat(MVHSTableau, ⊤, ∨(parseformula("p"), ⊥), G4) == true
@test alphasat(MVHSTableau, ⊤, ∨(parseformula("p"), α), G4) == true
@test alphasat(MVHSTableau, ⊤, ∨(parseformula("p"), β), G4) == true
@test alphasat(MVHSTableau, ⊤, ∨(parseformula("p"), ⊤), G4) == true

@test alphasat(MVHSTableau, ⊥, ∨(⊥, parseformula("p")), G4) == true
@test alphasat(MVHSTableau, ⊥, ∨(α, parseformula("p")), G4) == true
@test alphasat(MVHSTableau, ⊥, ∨(β, parseformula("p")), G4) == true
@test alphasat(MVHSTableau, ⊥, ∨(⊤, parseformula("p")), G4) == true
@test alphasat(MVHSTableau, α, ∨(⊥, parseformula("p")), G4) == true
@test alphasat(MVHSTableau, α, ∨(α, parseformula("p")), G4) == true
@test alphasat(MVHSTableau, α, ∨(β, parseformula("p")), G4) == true
@test alphasat(MVHSTableau, α, ∨(⊤, parseformula("p")), G4) == true
@test alphasat(MVHSTableau, β, ∨(⊥, parseformula("p")), G4) == true
@test alphasat(MVHSTableau, β, ∨(α, parseformula("p")), G4) == true
@test alphasat(MVHSTableau, β, ∨(β, parseformula("p")), G4) == true
@test alphasat(MVHSTableau, β, ∨(⊤, parseformula("p")), G4) == true
@test alphasat(MVHSTableau, ⊤, ∨(⊥, parseformula("p")), G4) == true
@test alphasat(MVHSTableau, ⊤, ∨(α, parseformula("p")), G4) == true
@test alphasat(MVHSTableau, ⊤, ∨(β, parseformula("p")), G4) == true
@test alphasat(MVHSTableau, ⊤, ∨(⊤, parseformula("p")), G4) == true

@test alphasat(MVHSTableau, ⊥, ∨(parseformula("p"), parseformula("p")), G4)
@test alphasat(MVHSTableau, α, ∨(parseformula("p"), parseformula("p")), G4)
@test alphasat(MVHSTableau, β, ∨(parseformula("p"), parseformula("p")), G4)
@test alphasat(MVHSTableau, ⊤, ∨(parseformula("p"), parseformula("p")), G4)

@test alphasat(MVHSTableau, ⊥, ∨(parseformula("p"), parseformula("q")), G4)
@test alphasat(MVHSTableau, α, ∨(parseformula("p"), parseformula("q")), G4)
@test alphasat(MVHSTableau, β, ∨(parseformula("p"), parseformula("q")), G4)
@test alphasat(MVHSTableau, ⊤, ∨(parseformula("p"), parseformula("q")), G4)

@test alphasat(MVHSTableau, ⊥, ∨(parseformula("q"), parseformula("q")), G4)
@test alphasat(MVHSTableau, α, ∨(parseformula("q"), parseformula("q")), G4)
@test alphasat(MVHSTableau, β, ∨(parseformula("q"), parseformula("q")), G4)
@test alphasat(MVHSTableau, ⊤, ∨(parseformula("q"), parseformula("q")), G4)

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

@test alphasat(MVHSTableau, ⊥, ∧(parseformula("p"), ⊥), G4) == true
@test alphasat(MVHSTableau, ⊥, ∧(parseformula("p"), α), G4) == true
@test alphasat(MVHSTableau, ⊥, ∧(parseformula("p"), β), G4) == true
@test alphasat(MVHSTableau, ⊥, ∧(parseformula("p"), ⊤), G4) == true
@test alphasat(MVHSTableau, α, ∧(parseformula("p"), ⊥), G4) == false
@test alphasat(MVHSTableau, α, ∧(parseformula("p"), α), G4) == true
@test alphasat(MVHSTableau, α, ∧(parseformula("p"), β), G4) == true
@test alphasat(MVHSTableau, α, ∧(parseformula("p"), ⊤), G4) == true
@test alphasat(MVHSTableau, β, ∧(parseformula("p"), ⊥), G4) == false
@test alphasat(MVHSTableau, β, ∧(parseformula("p"), α), G4) == false
@test alphasat(MVHSTableau, β, ∧(parseformula("p"), β), G4) == true
@test alphasat(MVHSTableau, β, ∧(parseformula("p"), ⊤), G4) == true
@test alphasat(MVHSTableau, ⊤, ∧(parseformula("p"), ⊥), G4) == false
@test alphasat(MVHSTableau, ⊤, ∧(parseformula("p"), α), G4) == false
@test alphasat(MVHSTableau, ⊤, ∧(parseformula("p"), β), G4) == false
@test alphasat(MVHSTableau, ⊤, ∧(parseformula("p"), ⊤), G4) == true

@test alphasat(MVHSTableau, ⊥, ∧(⊥, parseformula("p")), G4) == true
@test alphasat(MVHSTableau, ⊥, ∧(α, parseformula("p")), G4) == true
@test alphasat(MVHSTableau, ⊥, ∧(β, parseformula("p")), G4) == true
@test alphasat(MVHSTableau, ⊥, ∧(⊤, parseformula("p")), G4) == true
@test alphasat(MVHSTableau, α, ∧(⊥, parseformula("p")), G4) == false
@test alphasat(MVHSTableau, α, ∧(α, parseformula("p")), G4) == true
@test alphasat(MVHSTableau, α, ∧(β, parseformula("p")), G4) == true
@test alphasat(MVHSTableau, α, ∧(⊤, parseformula("p")), G4) == true
@test alphasat(MVHSTableau, β, ∧(⊥, parseformula("p")), G4) == false
@test alphasat(MVHSTableau, β, ∧(α, parseformula("p")), G4) == false
@test alphasat(MVHSTableau, β, ∧(β, parseformula("p")), G4) == true
@test alphasat(MVHSTableau, β, ∧(⊤, parseformula("p")), G4) == true
@test alphasat(MVHSTableau, ⊤, ∧(⊥, parseformula("p")), G4) == false
@test alphasat(MVHSTableau, ⊤, ∧(α, parseformula("p")), G4) == false
@test alphasat(MVHSTableau, ⊤, ∧(β, parseformula("p")), G4) == false
@test alphasat(MVHSTableau, ⊤, ∧(⊤, parseformula("p")), G4) == true

@test alphasat(MVHSTableau, ⊥, ∧(parseformula("p"), parseformula("p")), G4)
@test alphasat(MVHSTableau, α, ∧(parseformula("p"), parseformula("p")), G4)
@test alphasat(MVHSTableau, β, ∧(parseformula("p"), parseformula("p")), G4)
@test alphasat(MVHSTableau, ⊤, ∧(parseformula("p"), parseformula("p")), G4)

@test alphasat(MVHSTableau, ⊥, ∧(parseformula("p"), parseformula("q")), G4)
@test alphasat(MVHSTableau, α, ∧(parseformula("p"), parseformula("q")), G4)
@test alphasat(MVHSTableau, β, ∧(parseformula("p"), parseformula("q")), G4)
@test alphasat(MVHSTableau, ⊤, ∧(parseformula("p"), parseformula("q")), G4)

@test alphasat(MVHSTableau, ⊥, ∧(parseformula("q"), parseformula("p")), G4)
@test alphasat(MVHSTableau, α, ∧(parseformula("q"), parseformula("p")), G4)
@test alphasat(MVHSTableau, β, ∧(parseformula("q"), parseformula("p")), G4)
@test alphasat(MVHSTableau, ⊤, ∧(parseformula("q"), parseformula("p")), G4)

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

@test alphasat(MVHSTableau, ⊥, →(parseformula("p"), ⊥), G4) == true
@test alphasat(MVHSTableau, ⊥, →(parseformula("p"), α), G4) == true
@test alphasat(MVHSTableau, ⊥, →(parseformula("p"), β), G4) == true
@test alphasat(MVHSTableau, ⊥, →(parseformula("p"), ⊤), G4) == true
@test alphasat(MVHSTableau, α, →(parseformula("p"), ⊥), G4) == true
@test alphasat(MVHSTableau, α, →(parseformula("p"), α), G4) == true
@test alphasat(MVHSTableau, α, →(parseformula("p"), β), G4) == true
@test alphasat(MVHSTableau, α, →(parseformula("p"), ⊤), G4) == true
@test alphasat(MVHSTableau, β, →(parseformula("p"), ⊥), G4) == true
@test alphasat(MVHSTableau, β, →(parseformula("p"), α), G4) == true
@test alphasat(MVHSTableau, β, →(parseformula("p"), β), G4) == true
@test alphasat(MVHSTableau, β, →(parseformula("p"), ⊤), G4) == true
@test alphasat(MVHSTableau, ⊤, →(parseformula("p"), ⊥), G4) == true
@test alphasat(MVHSTableau, ⊤, →(parseformula("p"), α), G4) == true
@test alphasat(MVHSTableau, ⊤, →(parseformula("p"), β), G4) == true
@test alphasat(MVHSTableau, ⊤, →(parseformula("p"), ⊤), G4) == true

@test alphasat(MVHSTableau, ⊥, →(⊥, parseformula("p")), G4) == true
@test alphasat(MVHSTableau, ⊥, →(α, parseformula("p")), G4) == true
@test alphasat(MVHSTableau, ⊥, →(β, parseformula("p")), G4) == true
@test alphasat(MVHSTableau, ⊥, →(⊤, parseformula("p")), G4) == true
@test alphasat(MVHSTableau, α, →(⊥, parseformula("p")), G4) == true
@test alphasat(MVHSTableau, α, →(α, parseformula("p")), G4) == true
@test alphasat(MVHSTableau, α, →(β, parseformula("p")), G4) == true
@test alphasat(MVHSTableau, α, →(⊤, parseformula("p")), G4) == true
@test alphasat(MVHSTableau, β, →(⊥, parseformula("p")), G4) == true
@test alphasat(MVHSTableau, β, →(α, parseformula("p")), G4) == true
@test alphasat(MVHSTableau, β, →(β, parseformula("p")), G4) == true
@test alphasat(MVHSTableau, β, →(⊤, parseformula("p")), G4) == true
@test alphasat(MVHSTableau, ⊤, →(⊥, parseformula("p")), G4) == true
@test alphasat(MVHSTableau, ⊤, →(α, parseformula("p")), G4) == true
@test alphasat(MVHSTableau, ⊤, →(β, parseformula("p")), G4) == true
@test alphasat(MVHSTableau, ⊤, →(⊤, parseformula("p")), G4) == true

@test alphasat(MVHSTableau, ⊥, →(parseformula("p"), parseformula("p")), G4)
@test alphasat(MVHSTableau, α, →(parseformula("p"), parseformula("p")), G4)
@test alphasat(MVHSTableau, β, →(parseformula("p"), parseformula("p")), G4)
@test alphasat(MVHSTableau, ⊤, →(parseformula("p"), parseformula("p")), G4)

@test alphasat(MVHSTableau, ⊥, →(parseformula("p"), parseformula("q")), G4)
@test alphasat(MVHSTableau, α, →(parseformula("p"), parseformula("q")), G4)
@test alphasat(MVHSTableau, β, →(parseformula("p"), parseformula("q")), G4)
@test alphasat(MVHSTableau, ⊤, →(parseformula("p"), parseformula("q")), G4)

@test alphasat(MVHSTableau, ⊥, →(parseformula("q"), parseformula("p")), G4)
@test alphasat(MVHSTableau, α, →(parseformula("q"), parseformula("p")), G4)
@test alphasat(MVHSTableau, β, →(parseformula("q"), parseformula("p")), G4)
@test alphasat(MVHSTableau, ⊤, →(parseformula("q"), parseformula("p")), G4)

################################################################################
#### More difficult formulas ###################################################
################################################################################

@test alphasat(MVHSTableau, ⊤, booleantofuzzy(parseformula(
    "(x∨y∨z)∧(x∨y∨¬z)∧(x∨¬y∨z)∧(x∨¬y∨¬z)∧" *
    "(¬x∨y∨z)∧(¬x∨y∨¬z)∧(¬x∨¬y∨z)∧(¬x∨¬y∨¬z)"
)), G4) == false
