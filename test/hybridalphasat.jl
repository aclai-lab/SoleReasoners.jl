############################################################################################
#### G4 ####################################################################################
############################################################################################

using SoleLogics.ManyValuedLogics: G4
using SoleLogics.ManyValuedLogics: α, β

############################################################################################
## Base cases ##############################################################################
############################################################################################

@test hybridalphasat(⊥, ⊥, G4) == true
@test hybridalphasat(⊥, α, G4) == true
@test hybridalphasat(⊥, β, G4) == true
@test hybridalphasat(⊥, ⊤, G4) == true
@test hybridalphasat(α, ⊥, G4) == false
@test hybridalphasat(α, α, G4) == true
@test hybridalphasat(α, β, G4) == true
@test hybridalphasat(α, ⊤, G4) == true
@test hybridalphasat(β, ⊥, G4) == false
@test hybridalphasat(β, α, G4) == false
@test hybridalphasat(β, β, G4) == true
@test hybridalphasat(β, ⊤, G4) == true
@test hybridalphasat(⊤, ⊥, G4) == false
@test hybridalphasat(⊤, α, G4) == false
@test hybridalphasat(⊤, β, G4) == false
@test hybridalphasat(⊤, ⊤, G4) == true

@test hybridalphasat(⊥, parseformula("p"), G4) == true
@test hybridalphasat(α, parseformula("p"), G4) == true
@test hybridalphasat(β, parseformula("p"), G4) == true
@test hybridalphasat(⊤, parseformula("p"), G4) == true

############################################################################################
## (Strong) disjuction #####################################################################
############################################################################################

@test hybridalphasat(⊥, ∨(⊥, ⊥), G4) == true
@test hybridalphasat(⊥, ∨(⊥, α), G4) == true
@test hybridalphasat(⊥, ∨(⊥, β), G4) == true
@test hybridalphasat(⊥, ∨(⊥, ⊤), G4) == true
@test hybridalphasat(⊥, ∨(α, ⊥), G4) == true
@test hybridalphasat(⊥, ∨(α, α), G4) == true
@test hybridalphasat(⊥, ∨(α, β), G4) == true
@test hybridalphasat(⊥, ∨(α, ⊤), G4) == true
@test hybridalphasat(⊥, ∨(β, ⊥), G4) == true
@test hybridalphasat(⊥, ∨(β, α), G4) == true
@test hybridalphasat(⊥, ∨(β, β), G4) == true
@test hybridalphasat(⊥, ∨(β, ⊤), G4) == true
@test hybridalphasat(⊥, ∨(⊤, ⊥), G4) == true
@test hybridalphasat(⊥, ∨(⊤, α), G4) == true
@test hybridalphasat(⊥, ∨(⊤, β), G4) == true
@test hybridalphasat(⊥, ∨(⊤, ⊤), G4) == true

@test hybridalphasat(α, ∨(⊥, ⊥), G4) == false
@test hybridalphasat(α, ∨(⊥, α), G4) == true
@test hybridalphasat(α, ∨(⊥, β), G4) == true
@test hybridalphasat(α, ∨(⊥, ⊤), G4) == true
@test hybridalphasat(α, ∨(α, ⊥), G4) == true
@test hybridalphasat(α, ∨(α, α), G4) == true
@test hybridalphasat(α, ∨(α, β), G4) == true
@test hybridalphasat(α, ∨(α, ⊤), G4) == true
@test hybridalphasat(α, ∨(β, ⊥), G4) == true
@test hybridalphasat(α, ∨(β, α), G4) == true
@test hybridalphasat(α, ∨(β, β), G4) == true
@test hybridalphasat(α, ∨(β, ⊤), G4) == true
@test hybridalphasat(α, ∨(⊤, ⊥), G4) == true
@test hybridalphasat(α, ∨(⊤, α), G4) == true
@test hybridalphasat(α, ∨(⊤, β), G4) == true
@test hybridalphasat(α, ∨(⊤, ⊤), G4) == true

@test hybridalphasat(β, ∨(⊥, ⊥), G4) == false
@test hybridalphasat(β, ∨(⊥, α), G4) == false
@test hybridalphasat(β, ∨(⊥, β), G4) == true
@test hybridalphasat(β, ∨(⊥, ⊤), G4) == true
@test hybridalphasat(β, ∨(α, ⊥), G4) == false
@test hybridalphasat(β, ∨(α, α), G4) == false
@test hybridalphasat(β, ∨(α, β), G4) == true
@test hybridalphasat(β, ∨(α, ⊤), G4) == true
@test hybridalphasat(β, ∨(β, ⊥), G4) == true
@test hybridalphasat(β, ∨(β, α), G4) == true
@test hybridalphasat(β, ∨(β, β), G4) == true
@test hybridalphasat(β, ∨(β, ⊤), G4) == true
@test hybridalphasat(β, ∨(⊤, ⊥), G4) == true
@test hybridalphasat(β, ∨(⊤, α), G4) == true
@test hybridalphasat(β, ∨(⊤, β), G4) == true
@test hybridalphasat(β, ∨(⊤, ⊤), G4) == true

@test hybridalphasat(⊤, ∨(⊥, ⊥), G4) == false
@test hybridalphasat(⊤, ∨(⊥, α), G4) == false
@test hybridalphasat(⊤, ∨(⊥, β), G4) == false
@test hybridalphasat(⊤, ∨(⊥, ⊤), G4) == true
@test hybridalphasat(⊤, ∨(α, ⊥), G4) == false
@test hybridalphasat(⊤, ∨(α, α), G4) == false
@test hybridalphasat(⊤, ∨(α, β), G4) == false
@test hybridalphasat(⊤, ∨(α, ⊤), G4) == true
@test hybridalphasat(⊤, ∨(β, ⊥), G4) == false
@test hybridalphasat(⊤, ∨(β, α), G4) == false
@test hybridalphasat(⊤, ∨(β, β), G4) == false
@test hybridalphasat(⊤, ∨(β, ⊤), G4) == true
@test hybridalphasat(⊤, ∨(⊤, ⊥), G4) == true
@test hybridalphasat(⊤, ∨(⊤, α), G4) == true
@test hybridalphasat(⊤, ∨(⊤, β), G4) == true
@test hybridalphasat(⊤, ∨(⊤, ⊤), G4) == true

@test hybridalphasat(⊥, ∨(parseformula("p"), ⊥), G4) == true
@test hybridalphasat(⊥, ∨(parseformula("p"), α), G4) == true
@test hybridalphasat(⊥, ∨(parseformula("p"), β), G4) == true
@test hybridalphasat(⊥, ∨(parseformula("p"), ⊤), G4) == true
@test hybridalphasat(α, ∨(parseformula("p"), ⊥), G4) == true
@test hybridalphasat(α, ∨(parseformula("p"), α), G4) == true
@test hybridalphasat(α, ∨(parseformula("p"), β), G4) == true
@test hybridalphasat(α, ∨(parseformula("p"), ⊤), G4) == true
@test hybridalphasat(β, ∨(parseformula("p"), ⊥), G4) == true
@test hybridalphasat(β, ∨(parseformula("p"), α), G4) == true
@test hybridalphasat(β, ∨(parseformula("p"), β), G4) == true
@test hybridalphasat(β, ∨(parseformula("p"), ⊤), G4) == true
@test hybridalphasat(⊤, ∨(parseformula("p"), ⊥), G4) == true
@test hybridalphasat(⊤, ∨(parseformula("p"), α), G4) == true
@test hybridalphasat(⊤, ∨(parseformula("p"), β), G4) == true
@test hybridalphasat(⊤, ∨(parseformula("p"), ⊤), G4) == true

@test hybridalphasat(⊥, ∨(⊥, parseformula("p")), G4) == true
@test hybridalphasat(⊥, ∨(α, parseformula("p")), G4) == true
@test hybridalphasat(⊥, ∨(β, parseformula("p")), G4) == true
@test hybridalphasat(⊥, ∨(⊤, parseformula("p")), G4) == true
@test hybridalphasat(α, ∨(⊥, parseformula("p")), G4) == true
@test hybridalphasat(α, ∨(α, parseformula("p")), G4) == true
@test hybridalphasat(α, ∨(β, parseformula("p")), G4) == true
@test hybridalphasat(α, ∨(⊤, parseformula("p")), G4) == true
@test hybridalphasat(β, ∨(⊥, parseformula("p")), G4) == true
@test hybridalphasat(β, ∨(α, parseformula("p")), G4) == true
@test hybridalphasat(β, ∨(β, parseformula("p")), G4) == true
@test hybridalphasat(β, ∨(⊤, parseformula("p")), G4) == true
@test hybridalphasat(⊤, ∨(⊥, parseformula("p")), G4) == true
@test hybridalphasat(⊤, ∨(α, parseformula("p")), G4) == true
@test hybridalphasat(⊤, ∨(β, parseformula("p")), G4) == true
@test hybridalphasat(⊤, ∨(⊤, parseformula("p")), G4) == true

@test hybridalphasat(⊥, ∨(parseformula("p"), parseformula("p")), G4) == true
@test hybridalphasat(α, ∨(parseformula("p"), parseformula("p")), G4) == true
@test hybridalphasat(β, ∨(parseformula("p"), parseformula("p")), G4) == true
@test hybridalphasat(⊤, ∨(parseformula("p"), parseformula("p")), G4) == true

@test hybridalphasat(⊥, ∨(parseformula("p"), parseformula("q")), G4) == true
@test hybridalphasat(α, ∨(parseformula("p"), parseformula("q")), G4) == true
@test hybridalphasat(β, ∨(parseformula("p"), parseformula("q")), G4) == true
@test hybridalphasat(⊤, ∨(parseformula("p"), parseformula("q")), G4) == true

@test hybridalphasat(⊥, ∨(parseformula("q"), parseformula("q")), G4) == true
@test hybridalphasat(α, ∨(parseformula("q"), parseformula("q")), G4) == true
@test hybridalphasat(β, ∨(parseformula("q"), parseformula("q")), G4) == true
@test hybridalphasat(⊤, ∨(parseformula("q"), parseformula("q")), G4) == true

############################################################################################
## (Strong) conjunction ####################################################################
############################################################################################

@test hybridalphasat(⊥, ∧(⊥, ⊥), G4) == true
@test hybridalphasat(⊥, ∧(⊥, α), G4) == true
@test hybridalphasat(⊥, ∧(⊥, β), G4) == true
@test hybridalphasat(⊥, ∧(⊥, ⊤), G4) == true
@test hybridalphasat(⊥, ∧(α, ⊥), G4) == true
@test hybridalphasat(⊥, ∧(α, α), G4) == true
@test hybridalphasat(⊥, ∧(α, β), G4) == true
@test hybridalphasat(⊥, ∧(α, ⊤), G4) == true
@test hybridalphasat(⊥, ∧(β, ⊥), G4) == true
@test hybridalphasat(⊥, ∧(β, α), G4) == true
@test hybridalphasat(⊥, ∧(β, β), G4) == true
@test hybridalphasat(⊥, ∧(β, ⊤), G4) == true
@test hybridalphasat(⊥, ∧(⊤, ⊥), G4) == true
@test hybridalphasat(⊥, ∧(⊤, α), G4) == true
@test hybridalphasat(⊥, ∧(⊤, β), G4) == true
@test hybridalphasat(⊥, ∧(⊤, ⊤), G4) == true

@test hybridalphasat(α, ∧(⊥, ⊥), G4) == false
@test hybridalphasat(α, ∧(⊥, α), G4) == false
@test hybridalphasat(α, ∧(⊥, β), G4) == false
@test hybridalphasat(α, ∧(⊥, ⊤), G4) == false
@test hybridalphasat(α, ∧(α, ⊥), G4) == false
@test hybridalphasat(α, ∧(α, α), G4) == true
@test hybridalphasat(α, ∧(α, β), G4) == true
@test hybridalphasat(α, ∧(α, ⊤), G4) == true
@test hybridalphasat(α, ∧(β, ⊥), G4) == false
@test hybridalphasat(α, ∧(β, α), G4) == true
@test hybridalphasat(α, ∧(β, β), G4) == true
@test hybridalphasat(α, ∧(β, ⊤), G4) == true
@test hybridalphasat(α, ∧(⊤, ⊥), G4) == false
@test hybridalphasat(α, ∧(⊤, α), G4) == true
@test hybridalphasat(α, ∧(⊤, β), G4) == true
@test hybridalphasat(α, ∧(⊤, ⊤), G4) == true

@test hybridalphasat(β, ∧(⊥, ⊥), G4) == false
@test hybridalphasat(β, ∧(⊥, α), G4) == false
@test hybridalphasat(β, ∧(⊥, β), G4) == false
@test hybridalphasat(β, ∧(⊥, ⊤), G4) == false
@test hybridalphasat(β, ∧(α, ⊥), G4) == false
@test hybridalphasat(β, ∧(α, α), G4) == false
@test hybridalphasat(β, ∧(α, β), G4) == false
@test hybridalphasat(β, ∧(α, ⊤), G4) == false
@test hybridalphasat(β, ∧(β, ⊥), G4) == false
@test hybridalphasat(β, ∧(β, α), G4) == false
@test hybridalphasat(β, ∧(β, β), G4) == true
@test hybridalphasat(β, ∧(β, ⊤), G4) == true
@test hybridalphasat(β, ∧(⊤, ⊥), G4) == false
@test hybridalphasat(β, ∧(⊤, α), G4) == false
@test hybridalphasat(β, ∧(⊤, β), G4) == true
@test hybridalphasat(β, ∧(⊤, ⊤), G4) == true

@test hybridalphasat(⊤, ∧(⊥, ⊥), G4) == false
@test hybridalphasat(⊤, ∧(⊥, α), G4) == false
@test hybridalphasat(⊤, ∧(⊥, β), G4) == false
@test hybridalphasat(⊤, ∧(⊥, ⊤), G4) == false
@test hybridalphasat(⊤, ∧(α, ⊥), G4) == false
@test hybridalphasat(⊤, ∧(α, α), G4) == false
@test hybridalphasat(⊤, ∧(α, β), G4) == false
@test hybridalphasat(⊤, ∧(α, ⊤), G4) == false
@test hybridalphasat(⊤, ∧(β, ⊥), G4) == false
@test hybridalphasat(⊤, ∧(β, α), G4) == false
@test hybridalphasat(⊤, ∧(β, β), G4) == false
@test hybridalphasat(⊤, ∧(β, ⊤), G4) == false
@test hybridalphasat(⊤, ∧(⊤, ⊥), G4) == false
@test hybridalphasat(⊤, ∧(⊤, α), G4) == false
@test hybridalphasat(⊤, ∧(⊤, β), G4) == false
@test hybridalphasat(⊤, ∧(⊤, ⊤), G4) == true

@test hybridalphasat(⊥, ∧(parseformula("p"), ⊥), G4) == true
@test hybridalphasat(⊥, ∧(parseformula("p"), α), G4) == true
@test hybridalphasat(⊥, ∧(parseformula("p"), β), G4) == true
@test hybridalphasat(⊥, ∧(parseformula("p"), ⊤), G4) == true
@test hybridalphasat(α, ∧(parseformula("p"), ⊥), G4) == false
@test hybridalphasat(α, ∧(parseformula("p"), α), G4) == true
@test hybridalphasat(α, ∧(parseformula("p"), β), G4) == true
@test hybridalphasat(α, ∧(parseformula("p"), ⊤), G4) == true
@test hybridalphasat(β, ∧(parseformula("p"), ⊥), G4) == false
@test hybridalphasat(β, ∧(parseformula("p"), α), G4) == false
@test hybridalphasat(β, ∧(parseformula("p"), β), G4) == true
@test hybridalphasat(β, ∧(parseformula("p"), ⊤), G4) == true
@test hybridalphasat(⊤, ∧(parseformula("p"), ⊥), G4) == false
@test hybridalphasat(⊤, ∧(parseformula("p"), α), G4) == false
@test hybridalphasat(⊤, ∧(parseformula("p"), β), G4) == false
@test hybridalphasat(⊤, ∧(parseformula("p"), ⊤), G4) == true

@test hybridalphasat(⊥, ∧(⊥, parseformula("p")), G4) == true
@test hybridalphasat(⊥, ∧(α, parseformula("p")), G4) == true
@test hybridalphasat(⊥, ∧(β, parseformula("p")), G4) == true
@test hybridalphasat(⊥, ∧(⊤, parseformula("p")), G4) == true
@test hybridalphasat(α, ∧(⊥, parseformula("p")), G4) == false
@test hybridalphasat(α, ∧(α, parseformula("p")), G4) == true
@test hybridalphasat(α, ∧(β, parseformula("p")), G4) == true
@test hybridalphasat(α, ∧(⊤, parseformula("p")), G4) == true
@test hybridalphasat(β, ∧(⊥, parseformula("p")), G4) == false
@test hybridalphasat(β, ∧(α, parseformula("p")), G4) == false
@test hybridalphasat(β, ∧(β, parseformula("p")), G4) == true
@test hybridalphasat(β, ∧(⊤, parseformula("p")), G4) == true
@test hybridalphasat(⊤, ∧(⊥, parseformula("p")), G4) == false
@test hybridalphasat(⊤, ∧(α, parseformula("p")), G4) == false
@test hybridalphasat(⊤, ∧(β, parseformula("p")), G4) == false
@test hybridalphasat(⊤, ∧(⊤, parseformula("p")), G4) == true

@test hybridalphasat(⊥, ∧(parseformula("p"), parseformula("p")), G4) == true
@test hybridalphasat(α, ∧(parseformula("p"), parseformula("p")), G4) == true
@test hybridalphasat(β, ∧(parseformula("p"), parseformula("p")), G4) == true
@test hybridalphasat(⊤, ∧(parseformula("p"), parseformula("p")), G4) == true

@test hybridalphasat(⊥, ∧(parseformula("p"), parseformula("q")), G4) == true
@test hybridalphasat(α, ∧(parseformula("p"), parseformula("q")), G4) == true
@test hybridalphasat(β, ∧(parseformula("p"), parseformula("q")), G4) == true
@test hybridalphasat(⊤, ∧(parseformula("p"), parseformula("q")), G4) == true

@test hybridalphasat(⊥, ∧(parseformula("q"), parseformula("p")), G4) == true
@test hybridalphasat(α, ∧(parseformula("q"), parseformula("p")), G4) == true
@test hybridalphasat(β, ∧(parseformula("q"), parseformula("p")), G4) == true
@test hybridalphasat(⊤, ∧(parseformula("q"), parseformula("p")), G4) == true

############################################################################################
## Implication #############################################################################
############################################################################################

@test hybridalphasat(⊥, →(⊥, ⊥), G4) == true
@test hybridalphasat(⊥, →(⊥, α), G4) == true
@test hybridalphasat(⊥, →(⊥, β), G4) == true
@test hybridalphasat(⊥, →(⊥, ⊤), G4) == true
@test hybridalphasat(⊥, →(α, ⊥), G4) == true
@test hybridalphasat(⊥, →(α, α), G4) == true
@test hybridalphasat(⊥, →(α, β), G4) == true
@test hybridalphasat(⊥, →(α, ⊤), G4) == true
@test hybridalphasat(⊥, →(β, ⊥), G4) == true
@test hybridalphasat(⊥, →(β, α), G4) == true
@test hybridalphasat(⊥, →(β, β), G4) == true
@test hybridalphasat(⊥, →(β, ⊤), G4) == true
@test hybridalphasat(⊥, →(⊤, ⊥), G4) == true
@test hybridalphasat(⊥, →(⊤, α), G4) == true
@test hybridalphasat(⊥, →(⊤, β), G4) == true
@test hybridalphasat(⊥, →(⊤, ⊤), G4) == true

@test hybridalphasat(α, →(⊥, ⊥), G4) == true
@test hybridalphasat(α, →(⊥, α), G4) == true
@test hybridalphasat(α, →(⊥, β), G4) == true
@test hybridalphasat(α, →(⊥, ⊤), G4) == true
@test hybridalphasat(α, →(α, ⊥), G4) == false
@test hybridalphasat(α, →(α, α), G4) == true
@test hybridalphasat(α, →(α, β), G4) == true
@test hybridalphasat(α, →(α, ⊤), G4) == true
@test hybridalphasat(α, →(β, ⊥), G4) == false
@test hybridalphasat(α, →(β, α), G4) == true
@test hybridalphasat(α, →(β, β), G4) == true
@test hybridalphasat(α, →(β, ⊤), G4) == true
@test hybridalphasat(α, →(⊤, ⊥), G4) == false
@test hybridalphasat(α, →(⊤, α), G4) == true
@test hybridalphasat(α, →(⊤, β), G4) == true
@test hybridalphasat(α, →(⊤, ⊤), G4) == true

@test hybridalphasat(β, →(⊥, ⊥), G4) == true
@test hybridalphasat(β, →(⊥, α), G4) == true
@test hybridalphasat(β, →(⊥, β), G4) == true
@test hybridalphasat(β, →(⊥, ⊤), G4) == true
@test hybridalphasat(β, →(α, ⊥), G4) == false
@test hybridalphasat(β, →(α, α), G4) == true
@test hybridalphasat(β, →(α, β), G4) == true
@test hybridalphasat(β, →(α, ⊤), G4) == true
@test hybridalphasat(β, →(β, ⊥), G4) == false
@test hybridalphasat(β, →(β, α), G4) == false
@test hybridalphasat(β, →(β, β), G4) == true
@test hybridalphasat(β, →(β, ⊤), G4) == true
@test hybridalphasat(β, →(⊤, ⊥), G4) == false
@test hybridalphasat(β, →(⊤, α), G4) == false
@test hybridalphasat(β, →(⊤, β), G4) == true
@test hybridalphasat(β, →(⊤, ⊤), G4) == true

@test hybridalphasat(⊤, →(⊥, ⊥), G4) == true
@test hybridalphasat(⊤, →(⊥, α), G4) == true
@test hybridalphasat(⊤, →(⊥, β), G4) == true
@test hybridalphasat(⊤, →(⊥, ⊤), G4) == true
@test hybridalphasat(⊤, →(α, ⊥), G4) == false
@test hybridalphasat(⊤, →(α, α), G4) == true
@test hybridalphasat(⊤, →(α, β), G4) == true
@test hybridalphasat(⊤, →(α, ⊤), G4) == true
@test hybridalphasat(⊤, →(β, ⊥), G4) == false
@test hybridalphasat(⊤, →(β, α), G4) == false
@test hybridalphasat(⊤, →(β, β), G4) == true
@test hybridalphasat(⊤, →(β, ⊤), G4) == true
@test hybridalphasat(⊤, →(⊤, ⊥), G4) == false
@test hybridalphasat(⊤, →(⊤, α), G4) == false
@test hybridalphasat(⊤, →(⊤, β), G4) == false
@test hybridalphasat(⊤, →(⊤, ⊤), G4) == true

@test hybridalphasat(⊥, →(parseformula("p"), ⊥), G4) == true
@test hybridalphasat(⊥, →(parseformula("p"), α), G4) == true
@test hybridalphasat(⊥, →(parseformula("p"), β), G4) == true
@test hybridalphasat(⊥, →(parseformula("p"), ⊤), G4) == true
@test hybridalphasat(α, →(parseformula("p"), ⊥), G4) == true
@test hybridalphasat(α, →(parseformula("p"), α), G4) == true
@test hybridalphasat(α, →(parseformula("p"), β), G4) == true
@test hybridalphasat(α, →(parseformula("p"), ⊤), G4) == true
@test hybridalphasat(β, →(parseformula("p"), ⊥), G4) == true
@test hybridalphasat(β, →(parseformula("p"), α), G4) == true
@test hybridalphasat(β, →(parseformula("p"), β), G4) == true
@test hybridalphasat(β, →(parseformula("p"), ⊤), G4) == true
@test hybridalphasat(⊤, →(parseformula("p"), ⊥), G4) == true
@test hybridalphasat(⊤, →(parseformula("p"), α), G4) == true
@test hybridalphasat(⊤, →(parseformula("p"), β), G4) == true
@test hybridalphasat(⊤, →(parseformula("p"), ⊤), G4) == true

@test hybridalphasat(⊥, →(⊥, parseformula("p")), G4) == true
@test hybridalphasat(⊥, →(α, parseformula("p")), G4) == true
@test hybridalphasat(⊥, →(β, parseformula("p")), G4) == true
@test hybridalphasat(⊥, →(⊤, parseformula("p")), G4) == true
@test hybridalphasat(α, →(⊥, parseformula("p")), G4) == true
@test hybridalphasat(α, →(α, parseformula("p")), G4) == true
@test hybridalphasat(α, →(β, parseformula("p")), G4) == true
@test hybridalphasat(α, →(⊤, parseformula("p")), G4) == true
@test hybridalphasat(β, →(⊥, parseformula("p")), G4) == true
@test hybridalphasat(β, →(α, parseformula("p")), G4) == true
@test hybridalphasat(β, →(β, parseformula("p")), G4) == true
@test hybridalphasat(β, →(⊤, parseformula("p")), G4) == true
@test hybridalphasat(⊤, →(⊥, parseformula("p")), G4) == true
@test hybridalphasat(⊤, →(α, parseformula("p")), G4) == true
@test hybridalphasat(⊤, →(β, parseformula("p")), G4) == true
@test hybridalphasat(⊤, →(⊤, parseformula("p")), G4) == true

@test hybridalphasat(⊥, →(parseformula("p"), parseformula("p")), G4) == true
@test hybridalphasat(α, →(parseformula("p"), parseformula("p")), G4) == true
@test hybridalphasat(β, →(parseformula("p"), parseformula("p")), G4) == true
@test hybridalphasat(⊤, →(parseformula("p"), parseformula("p")), G4) == true

@test hybridalphasat(⊥, →(parseformula("p"), parseformula("q")), G4) == true
@test hybridalphasat(α, →(parseformula("p"), parseformula("q")), G4) == true
@test hybridalphasat(β, →(parseformula("p"), parseformula("q")), G4) == true
@test hybridalphasat(⊤, →(parseformula("p"), parseformula("q")), G4) == true

@test hybridalphasat(⊥, →(parseformula("q"), parseformula("p")), G4) == true
@test hybridalphasat(α, →(parseformula("q"), parseformula("p")), G4) == true
@test hybridalphasat(β, →(parseformula("q"), parseformula("p")), G4) == true
@test hybridalphasat(⊤, →(parseformula("q"), parseformula("p")), G4) == true

############################################################################################
#### Ł4 ####################################################################################
############################################################################################

using SoleLogics.ManyValuedLogics: Ł4
using SoleLogics.ManyValuedLogics: α, β

############################################################################################
## Base cases ##############################################################################
############################################################################################

@test hybridalphasat(⊥, ⊥, Ł4) == true
@test hybridalphasat(⊥, α, Ł4) == true
@test hybridalphasat(⊥, β, Ł4) == true
@test hybridalphasat(⊥, ⊤, Ł4) == true
@test hybridalphasat(α, ⊥, Ł4) == false
@test hybridalphasat(α, α, Ł4) == true
@test hybridalphasat(α, β, Ł4) == true
@test hybridalphasat(α, ⊤, Ł4) == true
@test hybridalphasat(β, ⊥, Ł4) == false
@test hybridalphasat(β, α, Ł4) == false
@test hybridalphasat(β, β, Ł4) == true
@test hybridalphasat(β, ⊤, Ł4) == true
@test hybridalphasat(⊤, ⊥, Ł4) == false
@test hybridalphasat(⊤, α, Ł4) == false
@test hybridalphasat(⊤, β, Ł4) == false
@test hybridalphasat(⊤, ⊤, Ł4) == true

@test hybridalphasat(⊥, parseformula("p"), Ł4) == true
@test hybridalphasat(α, parseformula("p"), Ł4) == true
@test hybridalphasat(β, parseformula("p"), Ł4) == true
@test hybridalphasat(⊤, parseformula("p"), Ł4) == true

############################################################################################
## (Strong) disjuction #####################################################################
############################################################################################

@test hybridalphasat(⊥, ∨(⊥, ⊥), Ł4) == true
@test hybridalphasat(⊥, ∨(⊥, α), Ł4) == true
@test hybridalphasat(⊥, ∨(⊥, β), Ł4) == true
@test hybridalphasat(⊥, ∨(⊥, ⊤), Ł4) == true
@test hybridalphasat(⊥, ∨(α, ⊥), Ł4) == true
@test hybridalphasat(⊥, ∨(α, α), Ł4) == true
@test hybridalphasat(⊥, ∨(α, β), Ł4) == true
@test hybridalphasat(⊥, ∨(α, ⊤), Ł4) == true
@test hybridalphasat(⊥, ∨(β, ⊥), Ł4) == true
@test hybridalphasat(⊥, ∨(β, α), Ł4) == true
@test hybridalphasat(⊥, ∨(β, β), Ł4) == true
@test hybridalphasat(⊥, ∨(β, ⊤), Ł4) == true
@test hybridalphasat(⊥, ∨(⊤, ⊥), Ł4) == true
@test hybridalphasat(⊥, ∨(⊤, α), Ł4) == true
@test hybridalphasat(⊥, ∨(⊤, β), Ł4) == true
@test hybridalphasat(⊥, ∨(⊤, ⊤), Ł4) == true

@test hybridalphasat(α, ∨(⊥, ⊥), Ł4) == false
@test hybridalphasat(α, ∨(⊥, α), Ł4) == true
@test hybridalphasat(α, ∨(⊥, β), Ł4) == true
@test hybridalphasat(α, ∨(⊥, ⊤), Ł4) == true
@test hybridalphasat(α, ∨(α, ⊥), Ł4) == true
@test hybridalphasat(α, ∨(α, α), Ł4) == true
@test hybridalphasat(α, ∨(α, β), Ł4) == true
@test hybridalphasat(α, ∨(α, ⊤), Ł4) == true
@test hybridalphasat(α, ∨(β, ⊥), Ł4) == true
@test hybridalphasat(α, ∨(β, α), Ł4) == true
@test hybridalphasat(α, ∨(β, β), Ł4) == true
@test hybridalphasat(α, ∨(β, ⊤), Ł4) == true
@test hybridalphasat(α, ∨(⊤, ⊥), Ł4) == true
@test hybridalphasat(α, ∨(⊤, α), Ł4) == true
@test hybridalphasat(α, ∨(⊤, β), Ł4) == true
@test hybridalphasat(α, ∨(⊤, ⊤), Ł4) == true

@test hybridalphasat(β, ∨(⊥, ⊥), Ł4) == false
@test hybridalphasat(β, ∨(⊥, α), Ł4) == false
@test hybridalphasat(β, ∨(⊥, β), Ł4) == true
@test hybridalphasat(β, ∨(⊥, ⊤), Ł4) == true
@test hybridalphasat(β, ∨(α, ⊥), Ł4) == false
@test hybridalphasat(β, ∨(α, α), Ł4) == false
@test hybridalphasat(β, ∨(α, β), Ł4) == true
@test hybridalphasat(β, ∨(α, ⊤), Ł4) == true
@test hybridalphasat(β, ∨(β, ⊥), Ł4) == true
@test hybridalphasat(β, ∨(β, α), Ł4) == true
@test hybridalphasat(β, ∨(β, β), Ł4) == true
@test hybridalphasat(β, ∨(β, ⊤), Ł4) == true
@test hybridalphasat(β, ∨(⊤, ⊥), Ł4) == true
@test hybridalphasat(β, ∨(⊤, α), Ł4) == true
@test hybridalphasat(β, ∨(⊤, β), Ł4) == true
@test hybridalphasat(β, ∨(⊤, ⊤), Ł4) == true

@test hybridalphasat(⊤, ∨(⊥, ⊥), Ł4) == false
@test hybridalphasat(⊤, ∨(⊥, α), Ł4) == false
@test hybridalphasat(⊤, ∨(⊥, β), Ł4) == false
@test hybridalphasat(⊤, ∨(⊥, ⊤), Ł4) == true
@test hybridalphasat(⊤, ∨(α, ⊥), Ł4) == false
@test hybridalphasat(⊤, ∨(α, α), Ł4) == false
@test hybridalphasat(⊤, ∨(α, β), Ł4) == false
@test hybridalphasat(⊤, ∨(α, ⊤), Ł4) == true
@test hybridalphasat(⊤, ∨(β, ⊥), Ł4) == false
@test hybridalphasat(⊤, ∨(β, α), Ł4) == false
@test hybridalphasat(⊤, ∨(β, β), Ł4) == false
@test hybridalphasat(⊤, ∨(β, ⊤), Ł4) == true
@test hybridalphasat(⊤, ∨(⊤, ⊥), Ł4) == true
@test hybridalphasat(⊤, ∨(⊤, α), Ł4) == true
@test hybridalphasat(⊤, ∨(⊤, β), Ł4) == true
@test hybridalphasat(⊤, ∨(⊤, ⊤), Ł4) == true

@test hybridalphasat(⊥, ∨(parseformula("p"), ⊥), Ł4) == true
@test hybridalphasat(⊥, ∨(parseformula("p"), α), Ł4) == true
@test hybridalphasat(⊥, ∨(parseformula("p"), β), Ł4) == true
@test hybridalphasat(⊥, ∨(parseformula("p"), ⊤), Ł4) == true
@test hybridalphasat(α, ∨(parseformula("p"), ⊥), Ł4) == true
@test hybridalphasat(α, ∨(parseformula("p"), α), Ł4) == true
@test hybridalphasat(α, ∨(parseformula("p"), β), Ł4) == true
@test hybridalphasat(α, ∨(parseformula("p"), ⊤), Ł4) == true
@test hybridalphasat(β, ∨(parseformula("p"), ⊥), Ł4) == true
@test hybridalphasat(β, ∨(parseformula("p"), α), Ł4) == true
@test hybridalphasat(β, ∨(parseformula("p"), β), Ł4) == true
@test hybridalphasat(β, ∨(parseformula("p"), ⊤), Ł4) == true
@test hybridalphasat(⊤, ∨(parseformula("p"), ⊥), Ł4) == true
@test hybridalphasat(⊤, ∨(parseformula("p"), α), Ł4) == true
@test hybridalphasat(⊤, ∨(parseformula("p"), β), Ł4) == true
@test hybridalphasat(⊤, ∨(parseformula("p"), ⊤), Ł4) == true

@test hybridalphasat(⊥, ∨(⊥, parseformula("p")), Ł4) == true
@test hybridalphasat(⊥, ∨(α, parseformula("p")), Ł4) == true
@test hybridalphasat(⊥, ∨(β, parseformula("p")), Ł4) == true
@test hybridalphasat(⊥, ∨(⊤, parseformula("p")), Ł4) == true
@test hybridalphasat(α, ∨(⊥, parseformula("p")), Ł4) == true
@test hybridalphasat(α, ∨(α, parseformula("p")), Ł4) == true
@test hybridalphasat(α, ∨(β, parseformula("p")), Ł4) == true
@test hybridalphasat(α, ∨(⊤, parseformula("p")), Ł4) == true
@test hybridalphasat(β, ∨(⊥, parseformula("p")), Ł4) == true
@test hybridalphasat(β, ∨(α, parseformula("p")), Ł4) == true
@test hybridalphasat(β, ∨(β, parseformula("p")), Ł4) == true
@test hybridalphasat(β, ∨(⊤, parseformula("p")), Ł4) == true
@test hybridalphasat(⊤, ∨(⊥, parseformula("p")), Ł4) == true
@test hybridalphasat(⊤, ∨(α, parseformula("p")), Ł4) == true
@test hybridalphasat(⊤, ∨(β, parseformula("p")), Ł4) == true
@test hybridalphasat(⊤, ∨(⊤, parseformula("p")), Ł4) == true

@test hybridalphasat(⊥, ∨(parseformula("p"), parseformula("p")), Ł4) == true
@test hybridalphasat(α, ∨(parseformula("p"), parseformula("p")), Ł4) == true
@test hybridalphasat(β, ∨(parseformula("p"), parseformula("p")), Ł4) == true
@test hybridalphasat(⊤, ∨(parseformula("p"), parseformula("p")), Ł4) == true

@test hybridalphasat(⊥, ∨(parseformula("p"), parseformula("q")), Ł4) == true
@test hybridalphasat(α, ∨(parseformula("p"), parseformula("q")), Ł4) == true
@test hybridalphasat(β, ∨(parseformula("p"), parseformula("q")), Ł4) == true
@test hybridalphasat(⊤, ∨(parseformula("p"), parseformula("q")), Ł4) == true

@test hybridalphasat(⊥, ∨(parseformula("q"), parseformula("q")), Ł4) == true
@test hybridalphasat(α, ∨(parseformula("q"), parseformula("q")), Ł4) == true
@test hybridalphasat(β, ∨(parseformula("q"), parseformula("q")), Ł4) == true
@test hybridalphasat(⊤, ∨(parseformula("q"), parseformula("q")), Ł4) == true

############################################################################################
## (Strong) conjunction ####################################################################
############################################################################################

@test hybridalphasat(⊥, ∧(⊥, ⊥), Ł4) == true
@test hybridalphasat(⊥, ∧(⊥, α), Ł4) == true
@test hybridalphasat(⊥, ∧(⊥, β), Ł4) == true
@test hybridalphasat(⊥, ∧(⊥, ⊤), Ł4) == true
@test hybridalphasat(⊥, ∧(α, ⊥), Ł4) == true
@test hybridalphasat(⊥, ∧(α, α), Ł4) == true
@test hybridalphasat(⊥, ∧(α, β), Ł4) == true
@test hybridalphasat(⊥, ∧(α, ⊤), Ł4) == true
@test hybridalphasat(⊥, ∧(β, ⊥), Ł4) == true
@test hybridalphasat(⊥, ∧(β, α), Ł4) == true
@test hybridalphasat(⊥, ∧(β, β), Ł4) == true
@test hybridalphasat(⊥, ∧(β, ⊤), Ł4) == true
@test hybridalphasat(⊥, ∧(⊤, ⊥), Ł4) == true
@test hybridalphasat(⊥, ∧(⊤, α), Ł4) == true
@test hybridalphasat(⊥, ∧(⊤, β), Ł4) == true
@test hybridalphasat(⊥, ∧(⊤, ⊤), Ł4) == true

@test hybridalphasat(α, ∧(⊥, ⊥), Ł4) == false
@test hybridalphasat(α, ∧(⊥, α), Ł4) == false
@test hybridalphasat(α, ∧(⊥, β), Ł4) == false
@test hybridalphasat(α, ∧(⊥, ⊤), Ł4) == false
@test hybridalphasat(α, ∧(α, ⊥), Ł4) == false
@test hybridalphasat(α, ∧(α, α), Ł4) == false
@test hybridalphasat(α, ∧(α, β), Ł4) == false
@test hybridalphasat(α, ∧(α, ⊤), Ł4) == true
@test hybridalphasat(α, ∧(β, ⊥), Ł4) == false
@test hybridalphasat(α, ∧(β, α), Ł4) == false
@test hybridalphasat(α, ∧(β, β), Ł4) == true
@test hybridalphasat(α, ∧(β, ⊤), Ł4) == true
@test hybridalphasat(α, ∧(⊤, ⊥), Ł4) == false
@test hybridalphasat(α, ∧(⊤, α), Ł4) == true
@test hybridalphasat(α, ∧(⊤, β), Ł4) == true
@test hybridalphasat(α, ∧(⊤, ⊤), Ł4) == true

@test hybridalphasat(β, ∧(⊥, ⊥), Ł4) == false
@test hybridalphasat(β, ∧(⊥, α), Ł4) == false
@test hybridalphasat(β, ∧(⊥, β), Ł4) == false
@test hybridalphasat(β, ∧(⊥, ⊤), Ł4) == false
@test hybridalphasat(β, ∧(α, ⊥), Ł4) == false
@test hybridalphasat(β, ∧(α, α), Ł4) == false
@test hybridalphasat(β, ∧(α, β), Ł4) == false
@test hybridalphasat(β, ∧(α, ⊤), Ł4) == false
@test hybridalphasat(β, ∧(β, ⊥), Ł4) == false
@test hybridalphasat(β, ∧(β, α), Ł4) == false
@test hybridalphasat(β, ∧(β, β), Ł4) == false
@test hybridalphasat(β, ∧(β, ⊤), Ł4) == true
@test hybridalphasat(β, ∧(⊤, ⊥), Ł4) == false
@test hybridalphasat(β, ∧(⊤, α), Ł4) == false
@test hybridalphasat(β, ∧(⊤, β), Ł4) == true
@test hybridalphasat(β, ∧(⊤, ⊤), Ł4) == true

@test hybridalphasat(⊤, ∧(⊥, ⊥), Ł4) == false
@test hybridalphasat(⊤, ∧(⊥, α), Ł4) == false
@test hybridalphasat(⊤, ∧(⊥, β), Ł4) == false
@test hybridalphasat(⊤, ∧(⊥, ⊤), Ł4) == false
@test hybridalphasat(⊤, ∧(α, ⊥), Ł4) == false
@test hybridalphasat(⊤, ∧(α, α), Ł4) == false
@test hybridalphasat(⊤, ∧(α, β), Ł4) == false
@test hybridalphasat(⊤, ∧(α, ⊤), Ł4) == false
@test hybridalphasat(⊤, ∧(β, ⊥), Ł4) == false
@test hybridalphasat(⊤, ∧(β, α), Ł4) == false
@test hybridalphasat(⊤, ∧(β, β), Ł4) == false
@test hybridalphasat(⊤, ∧(β, ⊤), Ł4) == false
@test hybridalphasat(⊤, ∧(⊤, ⊥), Ł4) == false
@test hybridalphasat(⊤, ∧(⊤, α), Ł4) == false
@test hybridalphasat(⊤, ∧(⊤, β), Ł4) == false
@test hybridalphasat(⊤, ∧(⊤, ⊤), Ł4) == true

@test hybridalphasat(⊥, ∧(parseformula("p"), ⊥), Ł4) == true
@test hybridalphasat(⊥, ∧(parseformula("p"), α), Ł4) == true
@test hybridalphasat(⊥, ∧(parseformula("p"), β), Ł4) == true
@test hybridalphasat(⊥, ∧(parseformula("p"), ⊤), Ł4) == true
@test hybridalphasat(α, ∧(parseformula("p"), ⊥), Ł4) == false
@test hybridalphasat(α, ∧(parseformula("p"), α), Ł4) == true
@test hybridalphasat(α, ∧(parseformula("p"), β), Ł4) == true
@test hybridalphasat(α, ∧(parseformula("p"), ⊤), Ł4) == true
@test hybridalphasat(β, ∧(parseformula("p"), ⊥), Ł4) == false
@test hybridalphasat(β, ∧(parseformula("p"), α), Ł4) == false
@test hybridalphasat(β, ∧(parseformula("p"), β), Ł4) == true
@test hybridalphasat(β, ∧(parseformula("p"), ⊤), Ł4) == true
@test hybridalphasat(⊤, ∧(parseformula("p"), ⊥), Ł4) == false
@test hybridalphasat(⊤, ∧(parseformula("p"), α), Ł4) == false
@test hybridalphasat(⊤, ∧(parseformula("p"), β), Ł4) == false
@test hybridalphasat(⊤, ∧(parseformula("p"), ⊤), Ł4) == true

@test hybridalphasat(⊥, ∧(⊥, parseformula("p")), Ł4) == true
@test hybridalphasat(⊥, ∧(α, parseformula("p")), Ł4) == true
@test hybridalphasat(⊥, ∧(β, parseformula("p")), Ł4) == true
@test hybridalphasat(⊥, ∧(⊤, parseformula("p")), Ł4) == true
@test hybridalphasat(α, ∧(⊥, parseformula("p")), Ł4) == false
@test hybridalphasat(α, ∧(α, parseformula("p")), Ł4) == true
@test hybridalphasat(α, ∧(β, parseformula("p")), Ł4) == true
@test hybridalphasat(α, ∧(⊤, parseformula("p")), Ł4) == true
@test hybridalphasat(β, ∧(⊥, parseformula("p")), Ł4) == false
@test hybridalphasat(β, ∧(α, parseformula("p")), Ł4) == false
@test hybridalphasat(β, ∧(β, parseformula("p")), Ł4) == true
@test hybridalphasat(β, ∧(⊤, parseformula("p")), Ł4) == true
@test hybridalphasat(⊤, ∧(⊥, parseformula("p")), Ł4) == false
@test hybridalphasat(⊤, ∧(α, parseformula("p")), Ł4) == false
@test hybridalphasat(⊤, ∧(β, parseformula("p")), Ł4) == false
@test hybridalphasat(⊤, ∧(⊤, parseformula("p")), Ł4) == true

@test hybridalphasat(⊥, ∧(parseformula("p"), parseformula("p")), Ł4) == true
@test hybridalphasat(α, ∧(parseformula("p"), parseformula("p")), Ł4) == true
@test hybridalphasat(β, ∧(parseformula("p"), parseformula("p")), Ł4) == true
@test hybridalphasat(⊤, ∧(parseformula("p"), parseformula("p")), Ł4) == true

@test hybridalphasat(⊥, ∧(parseformula("p"), parseformula("q")), Ł4) == true
@test hybridalphasat(α, ∧(parseformula("p"), parseformula("q")), Ł4) == true
@test hybridalphasat(β, ∧(parseformula("p"), parseformula("q")), Ł4) == true
@test hybridalphasat(⊤, ∧(parseformula("p"), parseformula("q")), Ł4) == true

@test hybridalphasat(⊥, ∧(parseformula("q"), parseformula("p")), Ł4) == true
@test hybridalphasat(α, ∧(parseformula("q"), parseformula("p")), Ł4) == true
@test hybridalphasat(β, ∧(parseformula("q"), parseformula("p")), Ł4) == true
@test hybridalphasat(⊤, ∧(parseformula("q"), parseformula("p")), Ł4) == true

############################################################################################
## Implication #############################################################################
############################################################################################

@test hybridalphasat(⊥, →(⊥, ⊥), Ł4) == true
@test hybridalphasat(⊥, →(⊥, α), Ł4) == true
@test hybridalphasat(⊥, →(⊥, β), Ł4) == true
@test hybridalphasat(⊥, →(⊥, ⊤), Ł4) == true
@test hybridalphasat(⊥, →(α, ⊥), Ł4) == true
@test hybridalphasat(⊥, →(α, α), Ł4) == true
@test hybridalphasat(⊥, →(α, β), Ł4) == true
@test hybridalphasat(⊥, →(α, ⊤), Ł4) == true
@test hybridalphasat(⊥, →(β, ⊥), Ł4) == true
@test hybridalphasat(⊥, →(β, α), Ł4) == true
@test hybridalphasat(⊥, →(β, β), Ł4) == true
@test hybridalphasat(⊥, →(β, ⊤), Ł4) == true
@test hybridalphasat(⊥, →(⊤, ⊥), Ł4) == true
@test hybridalphasat(⊥, →(⊤, α), Ł4) == true
@test hybridalphasat(⊥, →(⊤, β), Ł4) == true
@test hybridalphasat(⊥, →(⊤, ⊤), Ł4) == true

@test hybridalphasat(α, →(⊥, ⊥), Ł4) == true
@test hybridalphasat(α, →(⊥, α), Ł4) == true
@test hybridalphasat(α, →(⊥, β), Ł4) == true
@test hybridalphasat(α, →(⊥, ⊤), Ł4) == true
@test hybridalphasat(α, →(α, ⊥), Ł4) == true
@test hybridalphasat(α, →(α, α), Ł4) == true
@test hybridalphasat(α, →(α, β), Ł4) == true
@test hybridalphasat(α, →(α, ⊤), Ł4) == true
@test hybridalphasat(α, →(β, ⊥), Ł4) == true
@test hybridalphasat(α, →(β, α), Ł4) == true
@test hybridalphasat(α, →(β, β), Ł4) == true
@test hybridalphasat(α, →(β, ⊤), Ł4) == true
@test hybridalphasat(α, →(⊤, ⊥), Ł4) == false
@test hybridalphasat(α, →(⊤, α), Ł4) == true
@test hybridalphasat(α, →(⊤, β), Ł4) == true
@test hybridalphasat(α, →(⊤, ⊤), Ł4) == true

@test hybridalphasat(β, →(⊥, ⊥), Ł4) == true
@test hybridalphasat(β, →(⊥, α), Ł4) == true
@test hybridalphasat(β, →(⊥, β), Ł4) == true
@test hybridalphasat(β, →(⊥, ⊤), Ł4) == true
@test hybridalphasat(β, →(α, ⊥), Ł4) == true
@test hybridalphasat(β, →(α, α), Ł4) == true
@test hybridalphasat(β, →(α, β), Ł4) == true
@test hybridalphasat(β, →(α, ⊤), Ł4) == true
@test hybridalphasat(β, →(β, ⊥), Ł4) == false
@test hybridalphasat(β, →(β, α), Ł4) == true
@test hybridalphasat(β, →(β, β), Ł4) == true
@test hybridalphasat(β, →(β, ⊤), Ł4) == true
@test hybridalphasat(β, →(⊤, ⊥), Ł4) == false
@test hybridalphasat(β, →(⊤, α), Ł4) == false
@test hybridalphasat(β, →(⊤, β), Ł4) == true
@test hybridalphasat(β, →(⊤, ⊤), Ł4) == true

@test hybridalphasat(⊤, →(⊥, ⊥), Ł4) == true
@test hybridalphasat(⊤, →(⊥, α), Ł4) == true
@test hybridalphasat(⊤, →(⊥, β), Ł4) == true
@test hybridalphasat(⊤, →(⊥, ⊤), Ł4) == true
@test hybridalphasat(⊤, →(α, ⊥), Ł4) == false
@test hybridalphasat(⊤, →(α, α), Ł4) == true
@test hybridalphasat(⊤, →(α, β), Ł4) == true
@test hybridalphasat(⊤, →(α, ⊤), Ł4) == true
@test hybridalphasat(⊤, →(β, ⊥), Ł4) == false
@test hybridalphasat(⊤, →(β, α), Ł4) == false
@test hybridalphasat(⊤, →(β, β), Ł4) == true
@test hybridalphasat(⊤, →(β, ⊤), Ł4) == true
@test hybridalphasat(⊤, →(⊤, ⊥), Ł4) == false
@test hybridalphasat(⊤, →(⊤, α), Ł4) == false
@test hybridalphasat(⊤, →(⊤, β), Ł4) == false
@test hybridalphasat(⊤, →(⊤, ⊤), Ł4) == true

@test hybridalphasat(⊥, →(parseformula("p"), ⊥), G4) == true
@test hybridalphasat(⊥, →(parseformula("p"), α), G4) == true
@test hybridalphasat(⊥, →(parseformula("p"), β), G4) == true
@test hybridalphasat(⊥, →(parseformula("p"), ⊤), G4) == true
@test hybridalphasat(α, →(parseformula("p"), ⊥), G4) == true
@test hybridalphasat(α, →(parseformula("p"), α), G4) == true
@test hybridalphasat(α, →(parseformula("p"), β), G4) == true
@test hybridalphasat(α, →(parseformula("p"), ⊤), G4) == true
@test hybridalphasat(β, →(parseformula("p"), ⊥), G4) == true
@test hybridalphasat(β, →(parseformula("p"), α), G4) == true
@test hybridalphasat(β, →(parseformula("p"), β), G4) == true
@test hybridalphasat(β, →(parseformula("p"), ⊤), G4) == true
@test hybridalphasat(⊤, →(parseformula("p"), ⊥), G4) == true
@test hybridalphasat(⊤, →(parseformula("p"), α), G4) == true
@test hybridalphasat(⊤, →(parseformula("p"), β), G4) == true
@test hybridalphasat(⊤, →(parseformula("p"), ⊤), G4) == true

@test hybridalphasat(⊥, →(⊥, parseformula("p")), G4) == true
@test hybridalphasat(⊥, →(α, parseformula("p")), G4) == true
@test hybridalphasat(⊥, →(β, parseformula("p")), G4) == true
@test hybridalphasat(⊥, →(⊤, parseformula("p")), G4) == true
@test hybridalphasat(α, →(⊥, parseformula("p")), G4) == true
@test hybridalphasat(α, →(α, parseformula("p")), G4) == true
@test hybridalphasat(α, →(β, parseformula("p")), G4) == true
@test hybridalphasat(α, →(⊤, parseformula("p")), G4) == true
@test hybridalphasat(β, →(⊥, parseformula("p")), G4) == true
@test hybridalphasat(β, →(α, parseformula("p")), G4) == true
@test hybridalphasat(β, →(β, parseformula("p")), G4) == true
@test hybridalphasat(β, →(⊤, parseformula("p")), G4) == true
@test hybridalphasat(⊤, →(⊥, parseformula("p")), G4) == true
@test hybridalphasat(⊤, →(α, parseformula("p")), G4) == true
@test hybridalphasat(⊤, →(β, parseformula("p")), G4) == true
@test hybridalphasat(⊤, →(⊤, parseformula("p")), G4) == true

@test hybridalphasat(⊥, →(parseformula("p"), parseformula("p")), G4) == true
@test hybridalphasat(α, →(parseformula("p"), parseformula("p")), G4) == true
@test hybridalphasat(β, →(parseformula("p"), parseformula("p")), G4) == true
@test hybridalphasat(⊤, →(parseformula("p"), parseformula("p")), G4) == true

@test hybridalphasat(⊥, →(parseformula("p"), parseformula("q")), G4) == true
@test hybridalphasat(α, →(parseformula("p"), parseformula("q")), G4) == true
@test hybridalphasat(β, →(parseformula("p"), parseformula("q")), G4) == true
@test hybridalphasat(⊤, →(parseformula("p"), parseformula("q")), G4) == true

@test hybridalphasat(⊥, →(parseformula("q"), parseformula("p")), G4) == true
@test hybridalphasat(α, →(parseformula("q"), parseformula("p")), G4) == true
@test hybridalphasat(β, →(parseformula("q"), parseformula("p")), G4) == true
@test hybridalphasat(⊤, →(parseformula("q"), parseformula("p")), G4) == true

############################################################################################
#### H4 ####################################################################################
############################################################################################

using SoleLogics.ManyValuedLogics: H4
using SoleLogics.ManyValuedLogics: α, β

############################################################################################
## Base cases ##############################################################################
############################################################################################

@test hybridalphasat(⊥, ⊥, H4) == true
@test hybridalphasat(⊥, α, H4) == true
@test hybridalphasat(⊥, β, H4) == true
@test hybridalphasat(⊥, ⊤, H4) == true
@test hybridalphasat(α, ⊥, H4) == false
@test hybridalphasat(α, α, H4) == true
@test hybridalphasat(α, β, H4) == false
@test hybridalphasat(α, ⊤, H4) == true
@test hybridalphasat(β, ⊥, H4) == false
@test hybridalphasat(β, α, H4) == false
@test hybridalphasat(β, β, H4) == true
@test hybridalphasat(β, ⊤, H4) == true
@test hybridalphasat(⊤, ⊥, H4) == false
@test hybridalphasat(⊤, α, H4) == false
@test hybridalphasat(⊤, β, H4) == false
@test hybridalphasat(⊤, ⊤, H4) == true

@test hybridalphasat(⊥, parseformula("p"), H4) == true
@test hybridalphasat(α, parseformula("p"), H4) == true
@test hybridalphasat(β, parseformula("p"), H4) == true
@test hybridalphasat(⊤, parseformula("p"), H4) == true

############################################################################################
## (Strong) disjuction #####################################################################
############################################################################################

@test hybridalphasat(⊥, ∨(⊥, ⊥), H4) == true
@test hybridalphasat(⊥, ∨(⊥, α), H4) == true
@test hybridalphasat(⊥, ∨(⊥, β), H4) == true
@test hybridalphasat(⊥, ∨(⊥, ⊤), H4) == true
@test hybridalphasat(⊥, ∨(α, ⊥), H4) == true
@test hybridalphasat(⊥, ∨(α, α), H4) == true
@test hybridalphasat(⊥, ∨(α, β), H4) == true
@test hybridalphasat(⊥, ∨(α, ⊤), H4) == true
@test hybridalphasat(⊥, ∨(β, ⊥), H4) == true
@test hybridalphasat(⊥, ∨(β, α), H4) == true
@test hybridalphasat(⊥, ∨(β, β), H4) == true
@test hybridalphasat(⊥, ∨(β, ⊤), H4) == true
@test hybridalphasat(⊥, ∨(⊤, ⊥), H4) == true
@test hybridalphasat(⊥, ∨(⊤, α), H4) == true
@test hybridalphasat(⊥, ∨(⊤, β), H4) == true
@test hybridalphasat(⊥, ∨(⊤, ⊤), H4) == true

@test hybridalphasat(α, ∨(⊥, ⊥), H4) == false
@test hybridalphasat(α, ∨(⊥, α), H4) == true
@test hybridalphasat(α, ∨(⊥, β), H4) == false
@test hybridalphasat(α, ∨(⊥, ⊤), H4) == true
@test hybridalphasat(α, ∨(α, ⊥), H4) == true
@test hybridalphasat(α, ∨(α, α), H4) == true
@test hybridalphasat(α, ∨(α, β), H4) == true
@test hybridalphasat(α, ∨(α, ⊤), H4) == true
@test hybridalphasat(α, ∨(β, ⊥), H4) == false
@test hybridalphasat(α, ∨(β, α), H4) == true
@test hybridalphasat(α, ∨(β, β), H4) == false
@test hybridalphasat(α, ∨(β, ⊤), H4) == true
@test hybridalphasat(α, ∨(⊤, ⊥), H4) == true
@test hybridalphasat(α, ∨(⊤, α), H4) == true
@test hybridalphasat(α, ∨(⊤, β), H4) == true
@test hybridalphasat(α, ∨(⊤, ⊤), H4) == true

@test hybridalphasat(β, ∨(⊥, ⊥), H4) == false
@test hybridalphasat(β, ∨(⊥, α), H4) == false
@test hybridalphasat(β, ∨(⊥, β), H4) == true
@test hybridalphasat(β, ∨(⊥, ⊤), H4) == true
@test hybridalphasat(β, ∨(α, ⊥), H4) == false
@test hybridalphasat(β, ∨(α, α), H4) == false
@test hybridalphasat(β, ∨(α, β), H4) == true
@test hybridalphasat(β, ∨(α, ⊤), H4) == true
@test hybridalphasat(β, ∨(β, ⊥), H4) == true
@test hybridalphasat(β, ∨(β, α), H4) == true
@test hybridalphasat(β, ∨(β, β), H4) == true
@test hybridalphasat(β, ∨(β, ⊤), H4) == true
@test hybridalphasat(β, ∨(⊤, ⊥), H4) == true
@test hybridalphasat(β, ∨(⊤, α), H4) == true
@test hybridalphasat(β, ∨(⊤, β), H4) == true
@test hybridalphasat(β, ∨(⊤, ⊤), H4) == true

@test hybridalphasat(⊤, ∨(⊥, ⊥), H4) == false
@test hybridalphasat(⊤, ∨(⊥, α), H4) == false
@test hybridalphasat(⊤, ∨(⊥, β), H4) == false
@test hybridalphasat(⊤, ∨(⊥, ⊤), H4) == true
@test hybridalphasat(⊤, ∨(α, ⊥), H4) == false
@test hybridalphasat(⊤, ∨(α, α), H4) == false
@test hybridalphasat(⊤, ∨(α, β), H4) == true
@test hybridalphasat(⊤, ∨(α, ⊤), H4) == true
@test hybridalphasat(⊤, ∨(β, ⊥), H4) == false
@test hybridalphasat(⊤, ∨(β, α), H4) == true
@test hybridalphasat(⊤, ∨(β, β), H4) == false
@test hybridalphasat(⊤, ∨(β, ⊤), H4) == true
@test hybridalphasat(⊤, ∨(⊤, ⊥), H4) == true
@test hybridalphasat(⊤, ∨(⊤, α), H4) == true
@test hybridalphasat(⊤, ∨(⊤, β), H4) == true
@test hybridalphasat(⊤, ∨(⊤, ⊤), H4) == true

@test hybridalphasat(⊥, ∨(parseformula("p"), ⊥), H4) == true
@test hybridalphasat(⊥, ∨(parseformula("p"), α), H4) == true
@test hybridalphasat(⊥, ∨(parseformula("p"), β), H4) == true
@test hybridalphasat(⊥, ∨(parseformula("p"), ⊤), H4) == true
@test hybridalphasat(α, ∨(parseformula("p"), ⊥), H4) == true
@test hybridalphasat(α, ∨(parseformula("p"), α), H4) == true
@test hybridalphasat(α, ∨(parseformula("p"), β), H4) == true
@test hybridalphasat(α, ∨(parseformula("p"), ⊤), H4) == true
@test hybridalphasat(β, ∨(parseformula("p"), ⊥), H4) == true
@test hybridalphasat(β, ∨(parseformula("p"), α), H4) == true
@test hybridalphasat(β, ∨(parseformula("p"), β), H4) == true
@test hybridalphasat(β, ∨(parseformula("p"), ⊤), H4) == true
@test hybridalphasat(⊤, ∨(parseformula("p"), ⊥), H4) == true
@test hybridalphasat(⊤, ∨(parseformula("p"), α), H4) == true
@test hybridalphasat(⊤, ∨(parseformula("p"), β), H4) == true
@test hybridalphasat(⊤, ∨(parseformula("p"), ⊤), H4) == true

@test hybridalphasat(⊥, ∨(⊥, parseformula("p")), H4) == true
@test hybridalphasat(⊥, ∨(α, parseformula("p")), H4) == true
@test hybridalphasat(⊥, ∨(β, parseformula("p")), H4) == true
@test hybridalphasat(⊥, ∨(⊤, parseformula("p")), H4) == true
@test hybridalphasat(α, ∨(⊥, parseformula("p")), H4) == true
@test hybridalphasat(α, ∨(α, parseformula("p")), H4) == true
@test hybridalphasat(α, ∨(β, parseformula("p")), H4) == true
@test hybridalphasat(α, ∨(⊤, parseformula("p")), H4) == true
@test hybridalphasat(β, ∨(⊥, parseformula("p")), H4) == true
@test hybridalphasat(β, ∨(α, parseformula("p")), H4) == true
@test hybridalphasat(β, ∨(β, parseformula("p")), H4) == true
@test hybridalphasat(β, ∨(⊤, parseformula("p")), H4) == true
@test hybridalphasat(⊤, ∨(⊥, parseformula("p")), H4) == true
@test hybridalphasat(⊤, ∨(α, parseformula("p")), H4) == true
@test hybridalphasat(⊤, ∨(β, parseformula("p")), H4) == true
@test hybridalphasat(⊤, ∨(⊤, parseformula("p")), H4) == true

@test hybridalphasat(⊥, ∨(parseformula("p"), parseformula("p")), H4) == true
@test hybridalphasat(α, ∨(parseformula("p"), parseformula("p")), H4) == true
@test hybridalphasat(β, ∨(parseformula("p"), parseformula("p")), H4) == true
@test hybridalphasat(⊤, ∨(parseformula("p"), parseformula("p")), H4) == true

@test hybridalphasat(⊥, ∨(parseformula("p"), parseformula("q")), H4) == true
@test hybridalphasat(α, ∨(parseformula("p"), parseformula("q")), H4) == true
@test hybridalphasat(β, ∨(parseformula("p"), parseformula("q")), H4) == true
@test hybridalphasat(⊤, ∨(parseformula("p"), parseformula("q")), H4) == true

@test hybridalphasat(⊥, ∨(parseformula("q"), parseformula("q")), H4) == true
@test hybridalphasat(α, ∨(parseformula("q"), parseformula("q")), H4) == true
@test hybridalphasat(β, ∨(parseformula("q"), parseformula("q")), H4) == true
@test hybridalphasat(⊤, ∨(parseformula("q"), parseformula("q")), H4) == true

############################################################################################
## (Strong) conjunction ####################################################################
############################################################################################

@test hybridalphasat(⊥, ∧(⊥, ⊥), H4) == true
@test hybridalphasat(⊥, ∧(⊥, α), H4) == true
@test hybridalphasat(⊥, ∧(⊥, β), H4) == true
@test hybridalphasat(⊥, ∧(⊥, ⊤), H4) == true
@test hybridalphasat(⊥, ∧(α, ⊥), H4) == true
@test hybridalphasat(⊥, ∧(α, α), H4) == true
@test hybridalphasat(⊥, ∧(α, β), H4) == true
@test hybridalphasat(⊥, ∧(α, ⊤), H4) == true
@test hybridalphasat(⊥, ∧(β, ⊥), H4) == true
@test hybridalphasat(⊥, ∧(β, α), H4) == true
@test hybridalphasat(⊥, ∧(β, β), H4) == true
@test hybridalphasat(⊥, ∧(β, ⊤), H4) == true
@test hybridalphasat(⊥, ∧(⊤, ⊥), H4) == true
@test hybridalphasat(⊥, ∧(⊤, α), H4) == true
@test hybridalphasat(⊥, ∧(⊤, β), H4) == true
@test hybridalphasat(⊥, ∧(⊤, ⊤), H4) == true

@test hybridalphasat(α, ∧(⊥, ⊥), H4) == false
@test hybridalphasat(α, ∧(⊥, α), H4) == false
@test hybridalphasat(α, ∧(⊥, β), H4) == false
@test hybridalphasat(α, ∧(⊥, ⊤), H4) == false
@test hybridalphasat(α, ∧(α, ⊥), H4) == false
@test hybridalphasat(α, ∧(α, α), H4) == true
@test hybridalphasat(α, ∧(α, β), H4) == false
@test hybridalphasat(α, ∧(α, ⊤), H4) == true
@test hybridalphasat(α, ∧(β, ⊥), H4) == false
@test hybridalphasat(α, ∧(β, α), H4) == false
@test hybridalphasat(α, ∧(β, β), H4) == false
@test hybridalphasat(α, ∧(β, ⊤), H4) == false
@test hybridalphasat(α, ∧(⊤, ⊥), H4) == false
@test hybridalphasat(α, ∧(⊤, α), H4) == true
@test hybridalphasat(α, ∧(⊤, β), H4) == false
@test hybridalphasat(α, ∧(⊤, ⊤), H4) == true

@test hybridalphasat(β, ∧(⊥, ⊥), H4) == false
@test hybridalphasat(β, ∧(⊥, α), H4) == false
@test hybridalphasat(β, ∧(⊥, β), H4) == false
@test hybridalphasat(β, ∧(⊥, ⊤), H4) == false
@test hybridalphasat(β, ∧(α, ⊥), H4) == false
@test hybridalphasat(β, ∧(α, α), H4) == false
@test hybridalphasat(β, ∧(α, β), H4) == false
@test hybridalphasat(β, ∧(α, ⊤), H4) == false
@test hybridalphasat(β, ∧(β, ⊥), H4) == false
@test hybridalphasat(β, ∧(β, α), H4) == false
@test hybridalphasat(β, ∧(β, β), H4) == true
@test hybridalphasat(β, ∧(β, ⊤), H4) == true
@test hybridalphasat(β, ∧(⊤, ⊥), H4) == false
@test hybridalphasat(β, ∧(⊤, α), H4) == false
@test hybridalphasat(β, ∧(⊤, β), H4) == true
@test hybridalphasat(β, ∧(⊤, ⊤), H4) == true

@test hybridalphasat(⊤, ∧(⊥, ⊥), H4) == false
@test hybridalphasat(⊤, ∧(⊥, α), H4) == false
@test hybridalphasat(⊤, ∧(⊥, β), H4) == false
@test hybridalphasat(⊤, ∧(⊥, ⊤), H4) == false
@test hybridalphasat(⊤, ∧(α, ⊥), H4) == false
@test hybridalphasat(⊤, ∧(α, α), H4) == false
@test hybridalphasat(⊤, ∧(α, β), H4) == false
@test hybridalphasat(⊤, ∧(α, ⊤), H4) == false
@test hybridalphasat(⊤, ∧(β, ⊥), H4) == false
@test hybridalphasat(⊤, ∧(β, α), H4) == false
@test hybridalphasat(⊤, ∧(β, β), H4) == false
@test hybridalphasat(⊤, ∧(β, ⊤), H4) == false
@test hybridalphasat(⊤, ∧(⊤, ⊥), H4) == false
@test hybridalphasat(⊤, ∧(⊤, α), H4) == false
@test hybridalphasat(⊤, ∧(⊤, β), H4) == false
@test hybridalphasat(⊤, ∧(⊤, ⊤), H4) == true

@test hybridalphasat(⊥, ∧(parseformula("p"), ⊥), H4) == true
@test hybridalphasat(⊥, ∧(parseformula("p"), α), H4) == true
@test hybridalphasat(⊥, ∧(parseformula("p"), β), H4) == true
@test hybridalphasat(⊥, ∧(parseformula("p"), ⊤), H4) == true
@test hybridalphasat(α, ∧(parseformula("p"), ⊥), H4) == false
@test hybridalphasat(α, ∧(parseformula("p"), α), H4) == true
@test hybridalphasat(α, ∧(parseformula("p"), β), H4) == false
@test hybridalphasat(α, ∧(parseformula("p"), ⊤), H4) == true
@test hybridalphasat(β, ∧(parseformula("p"), ⊥), H4) == false
@test hybridalphasat(β, ∧(parseformula("p"), α), H4) == false
@test hybridalphasat(β, ∧(parseformula("p"), β), H4) == true
@test hybridalphasat(β, ∧(parseformula("p"), ⊤), H4) == true
@test hybridalphasat(⊤, ∧(parseformula("p"), ⊥), H4) == false
@test hybridalphasat(⊤, ∧(parseformula("p"), α), H4) == false
@test hybridalphasat(⊤, ∧(parseformula("p"), β), H4) == false
@test hybridalphasat(⊤, ∧(parseformula("p"), ⊤), H4) == true

@test hybridalphasat(⊥, ∧(⊥, parseformula("p")), H4) == true
@test hybridalphasat(⊥, ∧(α, parseformula("p")), H4) == true
@test hybridalphasat(⊥, ∧(β, parseformula("p")), H4) == true
@test hybridalphasat(⊥, ∧(⊤, parseformula("p")), H4) == true
@test hybridalphasat(α, ∧(⊥, parseformula("p")), H4) == false
@test hybridalphasat(α, ∧(α, parseformula("p")), H4) == true
@test hybridalphasat(α, ∧(β, parseformula("p")), H4) == false
@test hybridalphasat(α, ∧(⊤, parseformula("p")), H4) == true
@test hybridalphasat(β, ∧(⊥, parseformula("p")), H4) == false
@test hybridalphasat(β, ∧(α, parseformula("p")), H4) == false
@test hybridalphasat(β, ∧(β, parseformula("p")), H4) == true
@test hybridalphasat(β, ∧(⊤, parseformula("p")), H4) == true
@test hybridalphasat(⊤, ∧(⊥, parseformula("p")), H4) == false
@test hybridalphasat(⊤, ∧(α, parseformula("p")), H4) == false
@test hybridalphasat(⊤, ∧(β, parseformula("p")), H4) == false
@test hybridalphasat(⊤, ∧(⊤, parseformula("p")), H4) == true

@test hybridalphasat(⊥, ∧(parseformula("p"), parseformula("p")), H4) == true
@test hybridalphasat(α, ∧(parseformula("p"), parseformula("p")), H4) == true
@test hybridalphasat(β, ∧(parseformula("p"), parseformula("p")), H4) == true
@test hybridalphasat(⊤, ∧(parseformula("p"), parseformula("p")), H4) == true

@test hybridalphasat(⊥, ∧(parseformula("p"), parseformula("q")), H4) == true
@test hybridalphasat(α, ∧(parseformula("p"), parseformula("q")), H4) == true
@test hybridalphasat(β, ∧(parseformula("p"), parseformula("q")), H4) == true
@test hybridalphasat(⊤, ∧(parseformula("p"), parseformula("q")), H4) == true

@test hybridalphasat(⊥, ∧(parseformula("q"), parseformula("p")), H4) == true
@test hybridalphasat(α, ∧(parseformula("q"), parseformula("p")), H4) == true
@test hybridalphasat(β, ∧(parseformula("q"), parseformula("p")), H4) == true
@test hybridalphasat(⊤, ∧(parseformula("q"), parseformula("p")), H4) == true

############################################################################################
## Implication #############################################################################
############################################################################################

@test hybridalphasat(⊥, →(⊥, ⊥), H4) == true
@test hybridalphasat(⊥, →(⊥, α), H4) == true
@test hybridalphasat(⊥, →(⊥, β), H4) == true
@test hybridalphasat(⊥, →(⊥, ⊤), H4) == true
@test hybridalphasat(⊥, →(α, ⊥), H4) == true
@test hybridalphasat(⊥, →(α, α), H4) == true
@test hybridalphasat(⊥, →(α, β), H4) == true
@test hybridalphasat(⊥, →(α, ⊤), H4) == true
@test hybridalphasat(⊥, →(β, ⊥), H4) == true
@test hybridalphasat(⊥, →(β, α), H4) == true
@test hybridalphasat(⊥, →(β, β), H4) == true
@test hybridalphasat(⊥, →(β, ⊤), H4) == true
@test hybridalphasat(⊥, →(⊤, ⊥), H4) == true
@test hybridalphasat(⊥, →(⊤, α), H4) == true
@test hybridalphasat(⊥, →(⊤, β), H4) == true
@test hybridalphasat(⊥, →(⊤, ⊤), H4) == true

@test hybridalphasat(α, →(⊥, ⊥), H4) == true
@test hybridalphasat(α, →(⊥, α), H4) == true
@test hybridalphasat(α, →(⊥, β), H4) == true
@test hybridalphasat(α, →(⊥, ⊤), H4) == true
@test hybridalphasat(α, →(α, ⊥), H4) == false
@test hybridalphasat(α, →(α, α), H4) == true
@test hybridalphasat(α, →(α, β), H4) == false
@test hybridalphasat(α, →(α, ⊤), H4) == true
@test hybridalphasat(α, →(β, ⊥), H4) == true
@test hybridalphasat(α, →(β, α), H4) == true
@test hybridalphasat(α, →(β, β), H4) == true
@test hybridalphasat(α, →(β, ⊤), H4) == true
@test hybridalphasat(α, →(⊤, ⊥), H4) == false
@test hybridalphasat(α, →(⊤, α), H4) == true
@test hybridalphasat(α, →(⊤, β), H4) == false
@test hybridalphasat(α, →(⊤, ⊤), H4) == true

@test hybridalphasat(β, →(⊥, ⊥), H4) == true
@test hybridalphasat(β, →(⊥, α), H4) == true
@test hybridalphasat(β, →(⊥, β), H4) == true
@test hybridalphasat(β, →(⊥, ⊤), H4) == true
@test hybridalphasat(β, →(α, ⊥), H4) == true
@test hybridalphasat(β, →(α, α), H4) == true
@test hybridalphasat(β, →(α, β), H4) == true
@test hybridalphasat(β, →(α, ⊤), H4) == true
@test hybridalphasat(β, →(β, ⊥), H4) == false
@test hybridalphasat(β, →(β, α), H4) == false
@test hybridalphasat(β, →(β, β), H4) == true
@test hybridalphasat(β, →(β, ⊤), H4) == true
@test hybridalphasat(β, →(⊤, ⊥), H4) == false
@test hybridalphasat(β, →(⊤, α), H4) == false
@test hybridalphasat(β, →(⊤, β), H4) == true
@test hybridalphasat(β, →(⊤, ⊤), H4) == true

@test hybridalphasat(⊤, →(⊥, ⊥), H4) == true
@test hybridalphasat(⊤, →(⊥, α), H4) == true
@test hybridalphasat(⊤, →(⊥, β), H4) == true
@test hybridalphasat(⊤, →(⊥, ⊤), H4) == true
@test hybridalphasat(⊤, →(α, ⊥), H4) == false
@test hybridalphasat(⊤, →(α, α), H4) == true
@test hybridalphasat(⊤, →(α, β), H4) == false
@test hybridalphasat(⊤, →(α, ⊤), H4) == true
@test hybridalphasat(⊤, →(β, ⊥), H4) == false
@test hybridalphasat(⊤, →(β, α), H4) == false
@test hybridalphasat(⊤, →(β, β), H4) == true
@test hybridalphasat(⊤, →(β, ⊤), H4) == true
@test hybridalphasat(⊤, →(⊤, ⊥), H4) == false
@test hybridalphasat(⊤, →(⊤, α), H4) == false
@test hybridalphasat(⊤, →(⊤, β), H4) == false
@test hybridalphasat(⊤, →(⊤, ⊤), H4) == true

@test hybridalphasat(⊥, →(parseformula("p"), ⊥), H4) == true
@test hybridalphasat(⊥, →(parseformula("p"), α), H4) == true
@test hybridalphasat(⊥, →(parseformula("p"), β), H4) == true
@test hybridalphasat(⊥, →(parseformula("p"), ⊤), H4) == true
@test hybridalphasat(α, →(parseformula("p"), ⊥), H4) == true
@test hybridalphasat(α, →(parseformula("p"), α), H4) == true
@test hybridalphasat(α, →(parseformula("p"), β), H4) == true
@test hybridalphasat(α, →(parseformula("p"), ⊤), H4) == true
@test hybridalphasat(β, →(parseformula("p"), ⊥), H4) == true
@test hybridalphasat(β, →(parseformula("p"), α), H4) == true
@test hybridalphasat(β, →(parseformula("p"), β), H4) == true
@test hybridalphasat(β, →(parseformula("p"), ⊤), H4) == true
@test hybridalphasat(⊤, →(parseformula("p"), ⊥), H4) == true
@test hybridalphasat(⊤, →(parseformula("p"), α), H4) == true
@test hybridalphasat(⊤, →(parseformula("p"), β), H4) == true
@test hybridalphasat(⊤, →(parseformula("p"), ⊤), H4) == true

@test hybridalphasat(⊥, →(⊥, parseformula("p")), H4) == true
@test hybridalphasat(⊥, →(α, parseformula("p")), H4) == true
@test hybridalphasat(⊥, →(β, parseformula("p")), H4) == true
@test hybridalphasat(⊥, →(⊤, parseformula("p")), H4) == true
@test hybridalphasat(α, →(⊥, parseformula("p")), H4) == true
@test hybridalphasat(α, →(α, parseformula("p")), H4) == true
@test hybridalphasat(α, →(β, parseformula("p")), H4) == true
@test hybridalphasat(α, →(⊤, parseformula("p")), H4) == true
@test hybridalphasat(β, →(⊥, parseformula("p")), H4) == true
@test hybridalphasat(β, →(α, parseformula("p")), H4) == true
@test hybridalphasat(β, →(β, parseformula("p")), H4) == true
@test hybridalphasat(β, →(⊤, parseformula("p")), H4) == true
@test hybridalphasat(⊤, →(⊥, parseformula("p")), H4) == true
@test hybridalphasat(⊤, →(α, parseformula("p")), H4) == true
@test hybridalphasat(⊤, →(β, parseformula("p")), H4) == true
@test hybridalphasat(⊤, →(⊤, parseformula("p")), H4) == true

@test hybridalphasat(⊥, →(parseformula("p"), parseformula("p")), H4) == true
@test hybridalphasat(α, →(parseformula("p"), parseformula("p")), H4) == true
@test hybridalphasat(β, →(parseformula("p"), parseformula("p")), H4) == true
@test hybridalphasat(⊤, →(parseformula("p"), parseformula("p")), H4) == true

@test hybridalphasat(⊥, →(parseformula("p"), parseformula("q")), H4) == true
@test hybridalphasat(α, →(parseformula("p"), parseformula("q")), H4) == true
@test hybridalphasat(β, →(parseformula("p"), parseformula("q")), H4) == true
@test hybridalphasat(⊤, →(parseformula("p"), parseformula("q")), H4) == true

@test hybridalphasat(⊥, →(parseformula("q"), parseformula("p")), H4) == true
@test hybridalphasat(α, →(parseformula("q"), parseformula("p")), H4) == true
@test hybridalphasat(β, →(parseformula("q"), parseformula("p")), H4) == true
@test hybridalphasat(⊤, →(parseformula("q"), parseformula("p")), H4) == true
