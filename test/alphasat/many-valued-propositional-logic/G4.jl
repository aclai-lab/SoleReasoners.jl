using SoleReasoners: MVLTLFPTableau

################################################################################
#### G4 ########################################################################
################################################################################

using SoleLogics.ManyValuedLogics: G4
using SoleLogics.ManyValuedLogics: α, β

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

@test alphasat(MVLTLFPTableau, ⊥, parseformula("p"), G4) == true
@test alphasat(MVLTLFPTableau, α, parseformula("p"), G4) == true
@test alphasat(MVLTLFPTableau, β, parseformula("p"), G4) == true
@test alphasat(MVLTLFPTableau, ⊤, parseformula("p"), G4) == true

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

@test alphasat(MVLTLFPTableau, ⊥, ∨(parseformula("p"), ⊥), G4) == true
@test alphasat(MVLTLFPTableau, ⊥, ∨(parseformula("p"), α), G4) == true
@test alphasat(MVLTLFPTableau, ⊥, ∨(parseformula("p"), β), G4) == true
@test alphasat(MVLTLFPTableau, ⊥, ∨(parseformula("p"), ⊤), G4) == true
@test alphasat(MVLTLFPTableau, α, ∨(parseformula("p"), ⊥), G4) == true
@test alphasat(MVLTLFPTableau, α, ∨(parseformula("p"), α), G4) == true
@test alphasat(MVLTLFPTableau, α, ∨(parseformula("p"), β), G4) == true
@test alphasat(MVLTLFPTableau, α, ∨(parseformula("p"), ⊤), G4) == true
@test alphasat(MVLTLFPTableau, β, ∨(parseformula("p"), ⊥), G4) == true
@test alphasat(MVLTLFPTableau, β, ∨(parseformula("p"), α), G4) == true
@test alphasat(MVLTLFPTableau, β, ∨(parseformula("p"), β), G4) == true
@test alphasat(MVLTLFPTableau, β, ∨(parseformula("p"), ⊤), G4) == true
@test alphasat(MVLTLFPTableau, ⊤, ∨(parseformula("p"), ⊥), G4) == true
@test alphasat(MVLTLFPTableau, ⊤, ∨(parseformula("p"), α), G4) == true
@test alphasat(MVLTLFPTableau, ⊤, ∨(parseformula("p"), β), G4) == true
@test alphasat(MVLTLFPTableau, ⊤, ∨(parseformula("p"), ⊤), G4) == true

@test alphasat(MVLTLFPTableau, ⊥, ∨(⊥, parseformula("p")), G4) == true
@test alphasat(MVLTLFPTableau, ⊥, ∨(α, parseformula("p")), G4) == true
@test alphasat(MVLTLFPTableau, ⊥, ∨(β, parseformula("p")), G4) == true
@test alphasat(MVLTLFPTableau, ⊥, ∨(⊤, parseformula("p")), G4) == true
@test alphasat(MVLTLFPTableau, α, ∨(⊥, parseformula("p")), G4) == true
@test alphasat(MVLTLFPTableau, α, ∨(α, parseformula("p")), G4) == true
@test alphasat(MVLTLFPTableau, α, ∨(β, parseformula("p")), G4) == true
@test alphasat(MVLTLFPTableau, α, ∨(⊤, parseformula("p")), G4) == true
@test alphasat(MVLTLFPTableau, β, ∨(⊥, parseformula("p")), G4) == true
@test alphasat(MVLTLFPTableau, β, ∨(α, parseformula("p")), G4) == true
@test alphasat(MVLTLFPTableau, β, ∨(β, parseformula("p")), G4) == true
@test alphasat(MVLTLFPTableau, β, ∨(⊤, parseformula("p")), G4) == true
@test alphasat(MVLTLFPTableau, ⊤, ∨(⊥, parseformula("p")), G4) == true
@test alphasat(MVLTLFPTableau, ⊤, ∨(α, parseformula("p")), G4) == true
@test alphasat(MVLTLFPTableau, ⊤, ∨(β, parseformula("p")), G4) == true
@test alphasat(MVLTLFPTableau, ⊤, ∨(⊤, parseformula("p")), G4) == true

@test alphasat(MVLTLFPTableau, ⊥, ∨(parseformula("p"), parseformula("p")), G4)
@test alphasat(MVLTLFPTableau, α, ∨(parseformula("p"), parseformula("p")), G4)
@test alphasat(MVLTLFPTableau, β, ∨(parseformula("p"), parseformula("p")), G4)
@test alphasat(MVLTLFPTableau, ⊤, ∨(parseformula("p"), parseformula("p")), G4)

@test alphasat(MVLTLFPTableau, ⊥, ∨(parseformula("p"), parseformula("q")), G4)
@test alphasat(MVLTLFPTableau, α, ∨(parseformula("p"), parseformula("q")), G4)
@test alphasat(MVLTLFPTableau, β, ∨(parseformula("p"), parseformula("q")), G4)
@test alphasat(MVLTLFPTableau, ⊤, ∨(parseformula("p"), parseformula("q")), G4)

@test alphasat(MVLTLFPTableau, ⊥, ∨(parseformula("q"), parseformula("q")), G4)
@test alphasat(MVLTLFPTableau, α, ∨(parseformula("q"), parseformula("q")), G4)
@test alphasat(MVLTLFPTableau, β, ∨(parseformula("q"), parseformula("q")), G4)
@test alphasat(MVLTLFPTableau, ⊤, ∨(parseformula("q"), parseformula("q")), G4)

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

@test alphasat(MVLTLFPTableau, ⊥, ∧(parseformula("p"), ⊥), G4) == true
@test alphasat(MVLTLFPTableau, ⊥, ∧(parseformula("p"), α), G4) == true
@test alphasat(MVLTLFPTableau, ⊥, ∧(parseformula("p"), β), G4) == true
@test alphasat(MVLTLFPTableau, ⊥, ∧(parseformula("p"), ⊤), G4) == true
@test alphasat(MVLTLFPTableau, α, ∧(parseformula("p"), ⊥), G4) == false
@test alphasat(MVLTLFPTableau, α, ∧(parseformula("p"), α), G4) == true
@test alphasat(MVLTLFPTableau, α, ∧(parseformula("p"), β), G4) == true
@test alphasat(MVLTLFPTableau, α, ∧(parseformula("p"), ⊤), G4) == true
@test alphasat(MVLTLFPTableau, β, ∧(parseformula("p"), ⊥), G4) == false
@test alphasat(MVLTLFPTableau, β, ∧(parseformula("p"), α), G4) == false
@test alphasat(MVLTLFPTableau, β, ∧(parseformula("p"), β), G4) == true
@test alphasat(MVLTLFPTableau, β, ∧(parseformula("p"), ⊤), G4) == true
@test alphasat(MVLTLFPTableau, ⊤, ∧(parseformula("p"), ⊥), G4) == false
@test alphasat(MVLTLFPTableau, ⊤, ∧(parseformula("p"), α), G4) == false
@test alphasat(MVLTLFPTableau, ⊤, ∧(parseformula("p"), β), G4) == false
@test alphasat(MVLTLFPTableau, ⊤, ∧(parseformula("p"), ⊤), G4) == true

@test alphasat(MVLTLFPTableau, ⊥, ∧(⊥, parseformula("p")), G4) == true
@test alphasat(MVLTLFPTableau, ⊥, ∧(α, parseformula("p")), G4) == true
@test alphasat(MVLTLFPTableau, ⊥, ∧(β, parseformula("p")), G4) == true
@test alphasat(MVLTLFPTableau, ⊥, ∧(⊤, parseformula("p")), G4) == true
@test alphasat(MVLTLFPTableau, α, ∧(⊥, parseformula("p")), G4) == false
@test alphasat(MVLTLFPTableau, α, ∧(α, parseformula("p")), G4) == true
@test alphasat(MVLTLFPTableau, α, ∧(β, parseformula("p")), G4) == true
@test alphasat(MVLTLFPTableau, α, ∧(⊤, parseformula("p")), G4) == true
@test alphasat(MVLTLFPTableau, β, ∧(⊥, parseformula("p")), G4) == false
@test alphasat(MVLTLFPTableau, β, ∧(α, parseformula("p")), G4) == false
@test alphasat(MVLTLFPTableau, β, ∧(β, parseformula("p")), G4) == true
@test alphasat(MVLTLFPTableau, β, ∧(⊤, parseformula("p")), G4) == true
@test alphasat(MVLTLFPTableau, ⊤, ∧(⊥, parseformula("p")), G4) == false
@test alphasat(MVLTLFPTableau, ⊤, ∧(α, parseformula("p")), G4) == false
@test alphasat(MVLTLFPTableau, ⊤, ∧(β, parseformula("p")), G4) == false
@test alphasat(MVLTLFPTableau, ⊤, ∧(⊤, parseformula("p")), G4) == true

@test alphasat(MVLTLFPTableau, ⊥, ∧(parseformula("p"), parseformula("p")), G4)
@test alphasat(MVLTLFPTableau, α, ∧(parseformula("p"), parseformula("p")), G4)
@test alphasat(MVLTLFPTableau, β, ∧(parseformula("p"), parseformula("p")), G4)
@test alphasat(MVLTLFPTableau, ⊤, ∧(parseformula("p"), parseformula("p")), G4)

@test alphasat(MVLTLFPTableau, ⊥, ∧(parseformula("p"), parseformula("q")), G4)
@test alphasat(MVLTLFPTableau, α, ∧(parseformula("p"), parseformula("q")), G4)
@test alphasat(MVLTLFPTableau, β, ∧(parseformula("p"), parseformula("q")), G4)
@test alphasat(MVLTLFPTableau, ⊤, ∧(parseformula("p"), parseformula("q")), G4)

@test alphasat(MVLTLFPTableau, ⊥, ∧(parseformula("q"), parseformula("p")), G4)
@test alphasat(MVLTLFPTableau, α, ∧(parseformula("q"), parseformula("p")), G4)
@test alphasat(MVLTLFPTableau, β, ∧(parseformula("q"), parseformula("p")), G4)
@test alphasat(MVLTLFPTableau, ⊤, ∧(parseformula("q"), parseformula("p")), G4)

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

@test alphasat(MVLTLFPTableau, ⊥, →(parseformula("p"), ⊥), G4) == true
@test alphasat(MVLTLFPTableau, ⊥, →(parseformula("p"), α), G4) == true
@test alphasat(MVLTLFPTableau, ⊥, →(parseformula("p"), β), G4) == true
@test alphasat(MVLTLFPTableau, ⊥, →(parseformula("p"), ⊤), G4) == true
@test alphasat(MVLTLFPTableau, α, →(parseformula("p"), ⊥), G4) == true
@test alphasat(MVLTLFPTableau, α, →(parseformula("p"), α), G4) == true
@test alphasat(MVLTLFPTableau, α, →(parseformula("p"), β), G4) == true
@test alphasat(MVLTLFPTableau, α, →(parseformula("p"), ⊤), G4) == true
@test alphasat(MVLTLFPTableau, β, →(parseformula("p"), ⊥), G4) == true
@test alphasat(MVLTLFPTableau, β, →(parseformula("p"), α), G4) == true
@test alphasat(MVLTLFPTableau, β, →(parseformula("p"), β), G4) == true
@test alphasat(MVLTLFPTableau, β, →(parseformula("p"), ⊤), G4) == true
@test alphasat(MVLTLFPTableau, ⊤, →(parseformula("p"), ⊥), G4) == true
@test alphasat(MVLTLFPTableau, ⊤, →(parseformula("p"), α), G4) == true
@test alphasat(MVLTLFPTableau, ⊤, →(parseformula("p"), β), G4) == true
@test alphasat(MVLTLFPTableau, ⊤, →(parseformula("p"), ⊤), G4) == true

@test alphasat(MVLTLFPTableau, ⊥, →(⊥, parseformula("p")), G4) == true
@test alphasat(MVLTLFPTableau, ⊥, →(α, parseformula("p")), G4) == true
@test alphasat(MVLTLFPTableau, ⊥, →(β, parseformula("p")), G4) == true
@test alphasat(MVLTLFPTableau, ⊥, →(⊤, parseformula("p")), G4) == true
@test alphasat(MVLTLFPTableau, α, →(⊥, parseformula("p")), G4) == true
@test alphasat(MVLTLFPTableau, α, →(α, parseformula("p")), G4) == true
@test alphasat(MVLTLFPTableau, α, →(β, parseformula("p")), G4) == true
@test alphasat(MVLTLFPTableau, α, →(⊤, parseformula("p")), G4) == true
@test alphasat(MVLTLFPTableau, β, →(⊥, parseformula("p")), G4) == true
@test alphasat(MVLTLFPTableau, β, →(α, parseformula("p")), G4) == true
@test alphasat(MVLTLFPTableau, β, →(β, parseformula("p")), G4) == true
@test alphasat(MVLTLFPTableau, β, →(⊤, parseformula("p")), G4) == true
@test alphasat(MVLTLFPTableau, ⊤, →(⊥, parseformula("p")), G4) == true
@test alphasat(MVLTLFPTableau, ⊤, →(α, parseformula("p")), G4) == true
@test alphasat(MVLTLFPTableau, ⊤, →(β, parseformula("p")), G4) == true
@test alphasat(MVLTLFPTableau, ⊤, →(⊤, parseformula("p")), G4) == true

@test alphasat(MVLTLFPTableau, ⊥, →(parseformula("p"), parseformula("p")), G4)
@test alphasat(MVLTLFPTableau, α, →(parseformula("p"), parseformula("p")), G4)
@test alphasat(MVLTLFPTableau, β, →(parseformula("p"), parseformula("p")), G4)
@test alphasat(MVLTLFPTableau, ⊤, →(parseformula("p"), parseformula("p")), G4)

@test alphasat(MVLTLFPTableau, ⊥, →(parseformula("p"), parseformula("q")), G4)
@test alphasat(MVLTLFPTableau, α, →(parseformula("p"), parseformula("q")), G4)
@test alphasat(MVLTLFPTableau, β, →(parseformula("p"), parseformula("q")), G4)
@test alphasat(MVLTLFPTableau, ⊤, →(parseformula("p"), parseformula("q")), G4)

@test alphasat(MVLTLFPTableau, ⊥, →(parseformula("q"), parseformula("p")), G4)
@test alphasat(MVLTLFPTableau, α, →(parseformula("q"), parseformula("p")), G4)
@test alphasat(MVLTLFPTableau, β, →(parseformula("q"), parseformula("p")), G4)
@test alphasat(MVLTLFPTableau, ⊤, →(parseformula("q"), parseformula("p")), G4)

################################################################################
#### More difficult formulas ###################################################
################################################################################

@test alphasat(MVLTLFPTableau, ⊤, booleantofuzzy(parseformula(
    "(x∨y∨z)∧(x∨y∨¬z)∧(x∨¬y∨z)∧(x∨¬y∨¬z)∧" *
    "(¬x∨y∨z)∧(¬x∨y∨¬z)∧(¬x∨¬y∨z)∧(¬x∨¬y∨¬z)"
)), G4) == false
