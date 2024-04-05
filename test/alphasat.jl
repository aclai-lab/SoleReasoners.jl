
############################################################################################
#### G4 ####################################################################################
############################################################################################

include("algebras/g4.jl")

############################################################################################
## Base cases ##############################################################################
############################################################################################

@test alphasat(⊥, ⊥, G4) == true
@test alphasat(⊥, α, G4) == true
@test alphasat(⊥, β, G4) == true
@test alphasat(⊥, ⊤, G4) == true
@test alphasat(α, ⊥, G4) == false
@test alphasat(α, α, G4) == true
@test alphasat(α, β, G4) == true
@test alphasat(α, ⊤, G4) == true
@test alphasat(β, ⊥, G4) == false
@test alphasat(β, α, G4) == false
@test alphasat(β, β, G4) == true
@test alphasat(β, ⊤, G4) == true
@test alphasat(⊤, ⊥, G4) == false
@test alphasat(⊤, α, G4) == false
@test alphasat(⊤, β, G4) == false
@test alphasat(⊤, ⊤, G4) == true

@test alphasat(⊥, parseformula("p"), G4) == true
@test alphasat(α, parseformula("p"), G4) == true
@test alphasat(β, parseformula("p"), G4) == true
@test alphasat(⊤, parseformula("p"), G4) == true

############################################################################################
## (Strong) disjuction #####################################################################
############################################################################################

@test alphasat(⊥, ∨(⊥, ⊥), G4) == true
@test alphasat(⊥, ∨(⊥, α), G4) == true
@test alphasat(⊥, ∨(⊥, β), G4) == true
@test alphasat(⊥, ∨(⊥, ⊤), G4) == true
@test alphasat(⊥, ∨(α, ⊥), G4) == true
@test alphasat(⊥, ∨(α, α), G4) == true
@test alphasat(⊥, ∨(α, β), G4) == true
@test alphasat(⊥, ∨(α, ⊤), G4) == true
@test alphasat(⊥, ∨(β, ⊥), G4) == true
@test alphasat(⊥, ∨(β, α), G4) == true
@test alphasat(⊥, ∨(β, β), G4) == true
@test alphasat(⊥, ∨(β, ⊤), G4) == true
@test alphasat(⊥, ∨(⊤, ⊥), G4) == true
@test alphasat(⊥, ∨(⊤, α), G4) == true
@test alphasat(⊥, ∨(⊤, β), G4) == true
@test alphasat(⊥, ∨(⊤, ⊤), G4) == true

@test alphasat(α, ∨(⊥, ⊥), G4) == false
@test alphasat(α, ∨(⊥, α), G4) == true
@test alphasat(α, ∨(⊥, β), G4) == true
@test alphasat(α, ∨(⊥, ⊤), G4) == true
@test alphasat(α, ∨(α, ⊥), G4) == true
@test alphasat(α, ∨(α, α), G4) == true
@test alphasat(α, ∨(α, β), G4) == true
@test alphasat(α, ∨(α, ⊤), G4) == true
@test alphasat(α, ∨(β, ⊥), G4) == true
@test alphasat(α, ∨(β, α), G4) == true
@test alphasat(α, ∨(β, β), G4) == true
@test alphasat(α, ∨(β, ⊤), G4) == true
@test alphasat(α, ∨(⊤, ⊥), G4) == true
@test alphasat(α, ∨(⊤, α), G4) == true
@test alphasat(α, ∨(⊤, β), G4) == true
@test alphasat(α, ∨(⊤, ⊤), G4) == true

@test alphasat(β, ∨(⊥, ⊥), G4) == false
@test alphasat(β, ∨(⊥, α), G4) == false
@test alphasat(β, ∨(⊥, β), G4) == true
@test alphasat(β, ∨(⊥, ⊤), G4) == true
@test alphasat(β, ∨(α, ⊥), G4) == false
@test alphasat(β, ∨(α, α), G4) == false
@test alphasat(β, ∨(α, β), G4) == true
@test alphasat(β, ∨(α, ⊤), G4) == true
@test alphasat(β, ∨(β, ⊥), G4) == true
@test alphasat(β, ∨(β, α), G4) == true
@test alphasat(β, ∨(β, β), G4) == true
@test alphasat(β, ∨(β, ⊤), G4) == true
@test alphasat(β, ∨(⊤, ⊥), G4) == true
@test alphasat(β, ∨(⊤, α), G4) == true
@test alphasat(β, ∨(⊤, β), G4) == true
@test alphasat(β, ∨(⊤, ⊤), G4) == true

@test alphasat(⊤, ∨(⊥, ⊥), G4) == false
@test alphasat(⊤, ∨(⊥, α), G4) == false
@test alphasat(⊤, ∨(⊥, β), G4) == false
@test alphasat(⊤, ∨(⊥, ⊤), G4) == true
@test alphasat(⊤, ∨(α, ⊥), G4) == false
@test alphasat(⊤, ∨(α, α), G4) == false
@test alphasat(⊤, ∨(α, β), G4) == false
@test alphasat(⊤, ∨(α, ⊤), G4) == true
@test alphasat(⊤, ∨(β, ⊥), G4) == false
@test alphasat(⊤, ∨(β, α), G4) == false
@test alphasat(⊤, ∨(β, β), G4) == false
@test alphasat(⊤, ∨(β, ⊤), G4) == true
@test alphasat(⊤, ∨(⊤, ⊥), G4) == true
@test alphasat(⊤, ∨(⊤, α), G4) == true
@test alphasat(⊤, ∨(⊤, β), G4) == true
@test alphasat(⊤, ∨(⊤, ⊤), G4) == true

@test alphasat(⊥, ∨(parseformula("p"), ⊥), G4) == true
@test alphasat(⊥, ∨(parseformula("p"), α), G4) == true
@test alphasat(⊥, ∨(parseformula("p"), β), G4) == true
@test alphasat(⊥, ∨(parseformula("p"), ⊤), G4) == true
@test alphasat(α, ∨(parseformula("p"), ⊥), G4) == true
@test alphasat(α, ∨(parseformula("p"), α), G4) == true
@test alphasat(α, ∨(parseformula("p"), β), G4) == true
@test alphasat(α, ∨(parseformula("p"), ⊤), G4) == true
@test alphasat(β, ∨(parseformula("p"), ⊥), G4) == true
@test alphasat(β, ∨(parseformula("p"), α), G4) == true
@test alphasat(β, ∨(parseformula("p"), β), G4) == true
@test alphasat(β, ∨(parseformula("p"), ⊤), G4) == true
@test alphasat(⊤, ∨(parseformula("p"), ⊥), G4) == true
@test alphasat(⊤, ∨(parseformula("p"), α), G4) == true
@test alphasat(⊤, ∨(parseformula("p"), β), G4) == true
@test alphasat(⊤, ∨(parseformula("p"), ⊤), G4) == true

@test alphasat(⊥, ∨(⊥, parseformula("p")), G4) == true
@test alphasat(⊥, ∨(α, parseformula("p")), G4) == true
@test alphasat(⊥, ∨(β, parseformula("p")), G4) == true
@test alphasat(⊥, ∨(⊤, parseformula("p")), G4) == true
@test alphasat(α, ∨(⊥, parseformula("p")), G4) == true
@test alphasat(α, ∨(α, parseformula("p")), G4) == true
@test alphasat(α, ∨(β, parseformula("p")), G4) == true
@test alphasat(α, ∨(⊤, parseformula("p")), G4) == true
@test alphasat(β, ∨(⊥, parseformula("p")), G4) == true
@test alphasat(β, ∨(α, parseformula("p")), G4) == true
@test alphasat(β, ∨(β, parseformula("p")), G4) == true
@test alphasat(β, ∨(⊤, parseformula("p")), G4) == true
@test alphasat(⊤, ∨(⊥, parseformula("p")), G4) == true
@test alphasat(⊤, ∨(α, parseformula("p")), G4) == true
@test alphasat(⊤, ∨(β, parseformula("p")), G4) == true
@test alphasat(⊤, ∨(⊤, parseformula("p")), G4) == true

@test alphasat(⊥, ∨(parseformula("p"), parseformula("p")), G4) == true
@test alphasat(α, ∨(parseformula("p"), parseformula("p")), G4) == true
@test alphasat(β, ∨(parseformula("p"), parseformula("p")), G4) == true
@test alphasat(⊤, ∨(parseformula("p"), parseformula("p")), G4) == true

@test alphasat(⊥, ∨(parseformula("p"), parseformula("q")), G4) == true
@test alphasat(α, ∨(parseformula("p"), parseformula("q")), G4) == true
@test alphasat(β, ∨(parseformula("p"), parseformula("q")), G4) == true
@test alphasat(⊤, ∨(parseformula("p"), parseformula("q")), G4) == true

@test alphasat(⊥, ∨(parseformula("q"), parseformula("q")), G4) == true
@test alphasat(α, ∨(parseformula("q"), parseformula("q")), G4) == true
@test alphasat(β, ∨(parseformula("q"), parseformula("q")), G4) == true
@test alphasat(⊤, ∨(parseformula("q"), parseformula("q")), G4) == true

############################################################################################
## (Strong) conjunction ####################################################################
############################################################################################

@test alphasat(⊥, ∧(⊥, ⊥), G4) == true
@test alphasat(⊥, ∧(⊥, α), G4) == true
@test alphasat(⊥, ∧(⊥, β), G4) == true
@test alphasat(⊥, ∧(⊥, ⊤), G4) == true
@test alphasat(⊥, ∧(α, ⊥), G4) == true
@test alphasat(⊥, ∧(α, α), G4) == true
@test alphasat(⊥, ∧(α, β), G4) == true
@test alphasat(⊥, ∧(α, ⊤), G4) == true
@test alphasat(⊥, ∧(β, ⊥), G4) == true
@test alphasat(⊥, ∧(β, α), G4) == true
@test alphasat(⊥, ∧(β, β), G4) == true
@test alphasat(⊥, ∧(β, ⊤), G4) == true
@test alphasat(⊥, ∧(⊤, ⊥), G4) == true
@test alphasat(⊥, ∧(⊤, α), G4) == true
@test alphasat(⊥, ∧(⊤, β), G4) == true
@test alphasat(⊥, ∧(⊤, ⊤), G4) == true

@test alphasat(α, ∧(⊥, ⊥), G4) == false
@test alphasat(α, ∧(⊥, α), G4) == false
@test alphasat(α, ∧(⊥, β), G4) == false
@test alphasat(α, ∧(⊥, ⊤), G4) == false
@test alphasat(α, ∧(α, ⊥), G4) == false
@test alphasat(α, ∧(α, α), G4) == true
@test alphasat(α, ∧(α, β), G4) == true
@test alphasat(α, ∧(α, ⊤), G4) == true
@test alphasat(α, ∧(β, ⊥), G4) == false
@test alphasat(α, ∧(β, α), G4) == true
@test alphasat(α, ∧(β, β), G4) == true
@test alphasat(α, ∧(β, ⊤), G4) == true
@test alphasat(α, ∧(⊤, ⊥), G4) == false
@test alphasat(α, ∧(⊤, α), G4) == true
@test alphasat(α, ∧(⊤, β), G4) == true
@test alphasat(α, ∧(⊤, ⊤), G4) == true

@test alphasat(β, ∧(⊥, ⊥), G4) == false
@test alphasat(β, ∧(⊥, α), G4) == false
@test alphasat(β, ∧(⊥, β), G4) == false
@test alphasat(β, ∧(⊥, ⊤), G4) == false
@test alphasat(β, ∧(α, ⊥), G4) == false
@test alphasat(β, ∧(α, α), G4) == false
@test alphasat(β, ∧(α, β), G4) == false
@test alphasat(β, ∧(α, ⊤), G4) == false
@test alphasat(β, ∧(β, ⊥), G4) == false
@test alphasat(β, ∧(β, α), G4) == false
@test alphasat(β, ∧(β, β), G4) == true
@test alphasat(β, ∧(β, ⊤), G4) == true
@test alphasat(β, ∧(⊤, ⊥), G4) == false
@test alphasat(β, ∧(⊤, α), G4) == false
@test alphasat(β, ∧(⊤, β), G4) == true
@test alphasat(β, ∧(⊤, ⊤), G4) == true

@test alphasat(⊤, ∧(⊥, ⊥), G4) == false
@test alphasat(⊤, ∧(⊥, α), G4) == false
@test alphasat(⊤, ∧(⊥, β), G4) == false
@test alphasat(⊤, ∧(⊥, ⊤), G4) == false
@test alphasat(⊤, ∧(α, ⊥), G4) == false
@test alphasat(⊤, ∧(α, α), G4) == false
@test alphasat(⊤, ∧(α, β), G4) == false
@test alphasat(⊤, ∧(α, ⊤), G4) == false
@test alphasat(⊤, ∧(β, ⊥), G4) == false
@test alphasat(⊤, ∧(β, α), G4) == false
@test alphasat(⊤, ∧(β, β), G4) == false
@test alphasat(⊤, ∧(β, ⊤), G4) == false
@test alphasat(⊤, ∧(⊤, ⊥), G4) == false
@test alphasat(⊤, ∧(⊤, α), G4) == false
@test alphasat(⊤, ∧(⊤, β), G4) == false
@test alphasat(⊤, ∧(⊤, ⊤), G4) == true

@test alphasat(⊥, ∧(parseformula("p"), ⊥), G4) == true
@test alphasat(⊥, ∧(parseformula("p"), α), G4) == true
@test alphasat(⊥, ∧(parseformula("p"), β), G4) == true
@test alphasat(⊥, ∧(parseformula("p"), ⊤), G4) == true
@test alphasat(α, ∧(parseformula("p"), ⊥), G4) == false
@test alphasat(α, ∧(parseformula("p"), α), G4) == true
@test alphasat(α, ∧(parseformula("p"), β), G4) == true
@test alphasat(α, ∧(parseformula("p"), ⊤), G4) == true
@test alphasat(β, ∧(parseformula("p"), ⊥), G4) == false
@test alphasat(β, ∧(parseformula("p"), α), G4) == false
@test alphasat(β, ∧(parseformula("p"), β), G4) == true
@test alphasat(β, ∧(parseformula("p"), ⊤), G4) == true
@test alphasat(⊤, ∧(parseformula("p"), ⊥), G4) == false
@test alphasat(⊤, ∧(parseformula("p"), α), G4) == false
@test alphasat(⊤, ∧(parseformula("p"), β), G4) == false
@test alphasat(⊤, ∧(parseformula("p"), ⊤), G4) == true

@test alphasat(⊥, ∧(⊥, parseformula("p")), G4) == true
@test alphasat(⊥, ∧(α, parseformula("p")), G4) == true
@test alphasat(⊥, ∧(β, parseformula("p")), G4) == true
@test alphasat(⊥, ∧(⊤, parseformula("p")), G4) == true
@test alphasat(α, ∧(⊥, parseformula("p")), G4) == false
@test alphasat(α, ∧(α, parseformula("p")), G4) == true
@test alphasat(α, ∧(β, parseformula("p")), G4) == true
@test alphasat(α, ∧(⊤, parseformula("p")), G4) == true
@test alphasat(β, ∧(⊥, parseformula("p")), G4) == false
@test alphasat(β, ∧(α, parseformula("p")), G4) == false
@test alphasat(β, ∧(β, parseformula("p")), G4) == true
@test alphasat(β, ∧(⊤, parseformula("p")), G4) == true
@test alphasat(⊤, ∧(⊥, parseformula("p")), G4) == false
@test alphasat(⊤, ∧(α, parseformula("p")), G4) == false
@test alphasat(⊤, ∧(β, parseformula("p")), G4) == false
@test alphasat(⊤, ∧(⊤, parseformula("p")), G4) == true

@test alphasat(⊥, ∧(parseformula("p"), parseformula("p")), G4) == true
@test alphasat(α, ∧(parseformula("p"), parseformula("p")), G4) == true
@test alphasat(β, ∧(parseformula("p"), parseformula("p")), G4) == true
@test alphasat(⊤, ∧(parseformula("p"), parseformula("p")), G4) == true

@test alphasat(⊥, ∧(parseformula("p"), parseformula("q")), G4) == true
@test alphasat(α, ∧(parseformula("p"), parseformula("q")), G4) == true
@test alphasat(β, ∧(parseformula("p"), parseformula("q")), G4) == true
@test alphasat(⊤, ∧(parseformula("p"), parseformula("q")), G4) == true

@test alphasat(⊥, ∧(parseformula("q"), parseformula("p")), G4) == true
@test alphasat(α, ∧(parseformula("q"), parseformula("p")), G4) == true
@test alphasat(β, ∧(parseformula("q"), parseformula("p")), G4) == true
@test alphasat(⊤, ∧(parseformula("q"), parseformula("p")), G4) == true

############################################################################################
## Implication #############################################################################
############################################################################################

@test alphasat(⊥, →(⊥, ⊥), G4) == true
@test alphasat(⊥, →(⊥, α), G4) == true
@test alphasat(⊥, →(⊥, β), G4) == true
@test alphasat(⊥, →(⊥, ⊤), G4) == true
@test alphasat(⊥, →(α, ⊥), G4) == true
@test alphasat(⊥, →(α, α), G4) == true
@test alphasat(⊥, →(α, β), G4) == true
@test alphasat(⊥, →(α, ⊤), G4) == true
@test alphasat(⊥, →(β, ⊥), G4) == true
@test alphasat(⊥, →(β, α), G4) == true
@test alphasat(⊥, →(β, β), G4) == true
@test alphasat(⊥, →(β, ⊤), G4) == true
@test alphasat(⊥, →(⊤, ⊥), G4) == true
@test alphasat(⊥, →(⊤, α), G4) == true
@test alphasat(⊥, →(⊤, β), G4) == true
@test alphasat(⊥, →(⊤, ⊤), G4) == true

@test alphasat(α, →(⊥, ⊥), G4) == true
@test alphasat(α, →(⊥, α), G4) == true
@test alphasat(α, →(⊥, β), G4) == true
@test alphasat(α, →(⊥, ⊤), G4) == true
@test alphasat(α, →(α, ⊥), G4) == false
@test alphasat(α, →(α, α), G4) == true
@test alphasat(α, →(α, β), G4) == true
@test alphasat(α, →(α, ⊤), G4) == true
@test alphasat(α, →(β, ⊥), G4) == false
@test alphasat(α, →(β, α), G4) == true
@test alphasat(α, →(β, β), G4) == true
@test alphasat(α, →(β, ⊤), G4) == true
@test alphasat(α, →(⊤, ⊥), G4) == false
@test alphasat(α, →(⊤, α), G4) == true
@test alphasat(α, →(⊤, β), G4) == true
@test alphasat(α, →(⊤, ⊤), G4) == true

@test alphasat(β, →(⊥, ⊥), G4) == true
@test alphasat(β, →(⊥, α), G4) == true
@test alphasat(β, →(⊥, β), G4) == true
@test alphasat(β, →(⊥, ⊤), G4) == true
@test alphasat(β, →(α, ⊥), G4) == false
@test alphasat(β, →(α, α), G4) == true
@test alphasat(β, →(α, β), G4) == true
@test alphasat(β, →(α, ⊤), G4) == true
@test alphasat(β, →(β, ⊥), G4) == false
@test alphasat(β, →(β, α), G4) == false
@test alphasat(β, →(β, β), G4) == true
@test alphasat(β, →(β, ⊤), G4) == true
@test alphasat(β, →(⊤, ⊥), G4) == false
@test alphasat(β, →(⊤, α), G4) == false
@test alphasat(β, →(⊤, β), G4) == true
@test alphasat(β, →(⊤, ⊤), G4) == true

@test alphasat(⊤, →(⊥, ⊥), G4) == true
@test alphasat(⊤, →(⊥, α), G4) == true
@test alphasat(⊤, →(⊥, β), G4) == true
@test alphasat(⊤, →(⊥, ⊤), G4) == true
@test alphasat(⊤, →(α, ⊥), G4) == false
@test alphasat(⊤, →(α, α), G4) == true
@test alphasat(⊤, →(α, β), G4) == true
@test alphasat(⊤, →(α, ⊤), G4) == true
@test alphasat(⊤, →(β, ⊥), G4) == false
@test alphasat(⊤, →(β, α), G4) == false
@test alphasat(⊤, →(β, β), G4) == true
@test alphasat(⊤, →(β, ⊤), G4) == true
@test alphasat(⊤, →(⊤, ⊥), G4) == false
@test alphasat(⊤, →(⊤, α), G4) == false
@test alphasat(⊤, →(⊤, β), G4) == false
@test alphasat(⊤, →(⊤, ⊤), G4) == true

@test alphasat(⊥, →(parseformula("p"), ⊥), G4) == true
@test alphasat(⊥, →(parseformula("p"), α), G4) == true
@test alphasat(⊥, →(parseformula("p"), β), G4) == true
@test alphasat(⊥, →(parseformula("p"), ⊤), G4) == true
@test alphasat(α, →(parseformula("p"), ⊥), G4) == true
@test alphasat(α, →(parseformula("p"), α), G4) == true
@test alphasat(α, →(parseformula("p"), β), G4) == true
@test alphasat(α, →(parseformula("p"), ⊤), G4) == true
@test alphasat(β, →(parseformula("p"), ⊥), G4) == true
@test alphasat(β, →(parseformula("p"), α), G4) == true
@test alphasat(β, →(parseformula("p"), β), G4) == true
@test alphasat(β, →(parseformula("p"), ⊤), G4) == true
@test alphasat(⊤, →(parseformula("p"), ⊥), G4) == true
@test alphasat(⊤, →(parseformula("p"), α), G4) == true
@test alphasat(⊤, →(parseformula("p"), β), G4) == true
@test alphasat(⊤, →(parseformula("p"), ⊤), G4) == true

@test alphasat(⊥, →(⊥, parseformula("p")), G4) == true
@test alphasat(⊥, →(α, parseformula("p")), G4) == true
@test alphasat(⊥, →(β, parseformula("p")), G4) == true
@test alphasat(⊥, →(⊤, parseformula("p")), G4) == true
@test alphasat(α, →(⊥, parseformula("p")), G4) == true
@test alphasat(α, →(α, parseformula("p")), G4) == true
@test alphasat(α, →(β, parseformula("p")), G4) == true
@test alphasat(α, →(⊤, parseformula("p")), G4) == true
@test alphasat(β, →(⊥, parseformula("p")), G4) == true
@test alphasat(β, →(α, parseformula("p")), G4) == true
@test alphasat(β, →(β, parseformula("p")), G4) == true
@test alphasat(β, →(⊤, parseformula("p")), G4) == true
@test alphasat(⊤, →(⊥, parseformula("p")), G4) == true
@test alphasat(⊤, →(α, parseformula("p")), G4) == true
@test alphasat(⊤, →(β, parseformula("p")), G4) == true
@test alphasat(⊤, →(⊤, parseformula("p")), G4) == true

@test alphasat(⊥, →(parseformula("p"), parseformula("p")), G4) == true
@test alphasat(α, →(parseformula("p"), parseformula("p")), G4) == true
@test alphasat(β, →(parseformula("p"), parseformula("p")), G4) == true
@test alphasat(⊤, →(parseformula("p"), parseformula("p")), G4) == true

@test alphasat(⊥, →(parseformula("p"), parseformula("q")), G4) == true
@test alphasat(α, →(parseformula("p"), parseformula("q")), G4) == true
@test alphasat(β, →(parseformula("p"), parseformula("q")), G4) == true
@test alphasat(⊤, →(parseformula("p"), parseformula("q")), G4) == true

@test alphasat(⊥, →(parseformula("q"), parseformula("p")), G4) == true
@test alphasat(α, →(parseformula("q"), parseformula("p")), G4) == true
@test alphasat(β, →(parseformula("q"), parseformula("p")), G4) == true
@test alphasat(⊤, →(parseformula("q"), parseformula("p")), G4) == true

############################################################################################
#### Ł4 ####################################################################################
############################################################################################

include("algebras/l4.jl")

############################################################################################
## Base cases ##############################################################################
############################################################################################

@test alphasat(⊥, ⊥, Ł4) == true
@test alphasat(⊥, α, Ł4) == true
@test alphasat(⊥, β, Ł4) == true
@test alphasat(⊥, ⊤, Ł4) == true
@test alphasat(α, ⊥, Ł4) == false
@test alphasat(α, α, Ł4) == true
@test alphasat(α, β, Ł4) == true
@test alphasat(α, ⊤, Ł4) == true
@test alphasat(β, ⊥, Ł4) == false
@test alphasat(β, α, Ł4) == false
@test alphasat(β, β, Ł4) == true
@test alphasat(β, ⊤, Ł4) == true
@test alphasat(⊤, ⊥, Ł4) == false
@test alphasat(⊤, α, Ł4) == false
@test alphasat(⊤, β, Ł4) == false
@test alphasat(⊤, ⊤, Ł4) == true

@test alphasat(⊥, parseformula("p"), Ł4) == true
@test alphasat(α, parseformula("p"), Ł4) == true
@test alphasat(β, parseformula("p"), Ł4) == true
@test alphasat(⊤, parseformula("p"), Ł4) == true

############################################################################################
## (Strong) disjuction #####################################################################
############################################################################################

@test alphasat(⊥, ∨(⊥, ⊥), Ł4) == true
@test alphasat(⊥, ∨(⊥, α), Ł4) == true
@test alphasat(⊥, ∨(⊥, β), Ł4) == true
@test alphasat(⊥, ∨(⊥, ⊤), Ł4) == true
@test alphasat(⊥, ∨(α, ⊥), Ł4) == true
@test alphasat(⊥, ∨(α, α), Ł4) == true
@test alphasat(⊥, ∨(α, β), Ł4) == true
@test alphasat(⊥, ∨(α, ⊤), Ł4) == true
@test alphasat(⊥, ∨(β, ⊥), Ł4) == true
@test alphasat(⊥, ∨(β, α), Ł4) == true
@test alphasat(⊥, ∨(β, β), Ł4) == true
@test alphasat(⊥, ∨(β, ⊤), Ł4) == true
@test alphasat(⊥, ∨(⊤, ⊥), Ł4) == true
@test alphasat(⊥, ∨(⊤, α), Ł4) == true
@test alphasat(⊥, ∨(⊤, β), Ł4) == true
@test alphasat(⊥, ∨(⊤, ⊤), Ł4) == true

@test alphasat(α, ∨(⊥, ⊥), Ł4) == false
@test alphasat(α, ∨(⊥, α), Ł4) == true
@test alphasat(α, ∨(⊥, β), Ł4) == true
@test alphasat(α, ∨(⊥, ⊤), Ł4) == true
@test alphasat(α, ∨(α, ⊥), Ł4) == true
@test alphasat(α, ∨(α, α), Ł4) == true
@test alphasat(α, ∨(α, β), Ł4) == true
@test alphasat(α, ∨(α, ⊤), Ł4) == true
@test alphasat(α, ∨(β, ⊥), Ł4) == true
@test alphasat(α, ∨(β, α), Ł4) == true
@test alphasat(α, ∨(β, β), Ł4) == true
@test alphasat(α, ∨(β, ⊤), Ł4) == true
@test alphasat(α, ∨(⊤, ⊥), Ł4) == true
@test alphasat(α, ∨(⊤, α), Ł4) == true
@test alphasat(α, ∨(⊤, β), Ł4) == true
@test alphasat(α, ∨(⊤, ⊤), Ł4) == true

@test alphasat(β, ∨(⊥, ⊥), Ł4) == false
@test alphasat(β, ∨(⊥, α), Ł4) == false
@test alphasat(β, ∨(⊥, β), Ł4) == true
@test alphasat(β, ∨(⊥, ⊤), Ł4) == true
@test alphasat(β, ∨(α, ⊥), Ł4) == false
@test alphasat(β, ∨(α, α), Ł4) == false
@test alphasat(β, ∨(α, β), Ł4) == true
@test alphasat(β, ∨(α, ⊤), Ł4) == true
@test alphasat(β, ∨(β, ⊥), Ł4) == true
@test alphasat(β, ∨(β, α), Ł4) == true
@test alphasat(β, ∨(β, β), Ł4) == true
@test alphasat(β, ∨(β, ⊤), Ł4) == true
@test alphasat(β, ∨(⊤, ⊥), Ł4) == true
@test alphasat(β, ∨(⊤, α), Ł4) == true
@test alphasat(β, ∨(⊤, β), Ł4) == true
@test alphasat(β, ∨(⊤, ⊤), Ł4) == true

@test alphasat(⊤, ∨(⊥, ⊥), Ł4) == false
@test alphasat(⊤, ∨(⊥, α), Ł4) == false
@test alphasat(⊤, ∨(⊥, β), Ł4) == false
@test alphasat(⊤, ∨(⊥, ⊤), Ł4) == true
@test alphasat(⊤, ∨(α, ⊥), Ł4) == false
@test alphasat(⊤, ∨(α, α), Ł4) == false
@test alphasat(⊤, ∨(α, β), Ł4) == false
@test alphasat(⊤, ∨(α, ⊤), Ł4) == true
@test alphasat(⊤, ∨(β, ⊥), Ł4) == false
@test alphasat(⊤, ∨(β, α), Ł4) == false
@test alphasat(⊤, ∨(β, β), Ł4) == false
@test alphasat(⊤, ∨(β, ⊤), Ł4) == true
@test alphasat(⊤, ∨(⊤, ⊥), Ł4) == true
@test alphasat(⊤, ∨(⊤, α), Ł4) == true
@test alphasat(⊤, ∨(⊤, β), Ł4) == true
@test alphasat(⊤, ∨(⊤, ⊤), Ł4) == true

@test alphasat(⊥, ∨(parseformula("p"), ⊥), Ł4) == true
@test alphasat(⊥, ∨(parseformula("p"), α), Ł4) == true
@test alphasat(⊥, ∨(parseformula("p"), β), Ł4) == true
@test alphasat(⊥, ∨(parseformula("p"), ⊤), Ł4) == true
@test alphasat(α, ∨(parseformula("p"), ⊥), Ł4) == true
@test alphasat(α, ∨(parseformula("p"), α), Ł4) == true
@test alphasat(α, ∨(parseformula("p"), β), Ł4) == true
@test alphasat(α, ∨(parseformula("p"), ⊤), Ł4) == true
@test alphasat(β, ∨(parseformula("p"), ⊥), Ł4) == true
@test alphasat(β, ∨(parseformula("p"), α), Ł4) == true
@test alphasat(β, ∨(parseformula("p"), β), Ł4) == true
@test alphasat(β, ∨(parseformula("p"), ⊤), Ł4) == true
@test alphasat(⊤, ∨(parseformula("p"), ⊥), Ł4) == true
@test alphasat(⊤, ∨(parseformula("p"), α), Ł4) == true
@test alphasat(⊤, ∨(parseformula("p"), β), Ł4) == true
@test alphasat(⊤, ∨(parseformula("p"), ⊤), Ł4) == true

@test alphasat(⊥, ∨(⊥, parseformula("p")), Ł4) == true
@test alphasat(⊥, ∨(α, parseformula("p")), Ł4) == true
@test alphasat(⊥, ∨(β, parseformula("p")), Ł4) == true
@test alphasat(⊥, ∨(⊤, parseformula("p")), Ł4) == true
@test alphasat(α, ∨(⊥, parseformula("p")), Ł4) == true
@test alphasat(α, ∨(α, parseformula("p")), Ł4) == true
@test alphasat(α, ∨(β, parseformula("p")), Ł4) == true
@test alphasat(α, ∨(⊤, parseformula("p")), Ł4) == true
@test alphasat(β, ∨(⊥, parseformula("p")), Ł4) == true
@test alphasat(β, ∨(α, parseformula("p")), Ł4) == true
@test alphasat(β, ∨(β, parseformula("p")), Ł4) == true
@test alphasat(β, ∨(⊤, parseformula("p")), Ł4) == true
@test alphasat(⊤, ∨(⊥, parseformula("p")), Ł4) == true
@test alphasat(⊤, ∨(α, parseformula("p")), Ł4) == true
@test alphasat(⊤, ∨(β, parseformula("p")), Ł4) == true
@test alphasat(⊤, ∨(⊤, parseformula("p")), Ł4) == true

@test alphasat(⊥, ∨(parseformula("p"), parseformula("p")), Ł4) == true
@test alphasat(α, ∨(parseformula("p"), parseformula("p")), Ł4) == true
@test alphasat(β, ∨(parseformula("p"), parseformula("p")), Ł4) == true
@test alphasat(⊤, ∨(parseformula("p"), parseformula("p")), Ł4) == true

@test alphasat(⊥, ∨(parseformula("p"), parseformula("q")), Ł4) == true
@test alphasat(α, ∨(parseformula("p"), parseformula("q")), Ł4) == true
@test alphasat(β, ∨(parseformula("p"), parseformula("q")), Ł4) == true
@test alphasat(⊤, ∨(parseformula("p"), parseformula("q")), Ł4) == true

@test alphasat(⊥, ∨(parseformula("q"), parseformula("q")), Ł4) == true
@test alphasat(α, ∨(parseformula("q"), parseformula("q")), Ł4) == true
@test alphasat(β, ∨(parseformula("q"), parseformula("q")), Ł4) == true
@test alphasat(⊤, ∨(parseformula("q"), parseformula("q")), Ł4) == true

############################################################################################
## (Strong) conjunction ####################################################################
############################################################################################

@test alphasat(⊥, ∧(⊥, ⊥), Ł4) == true
@test alphasat(⊥, ∧(⊥, α), Ł4) == true
@test alphasat(⊥, ∧(⊥, β), Ł4) == true
@test alphasat(⊥, ∧(⊥, ⊤), Ł4) == true
@test alphasat(⊥, ∧(α, ⊥), Ł4) == true
@test alphasat(⊥, ∧(α, α), Ł4) == true
@test alphasat(⊥, ∧(α, β), Ł4) == true
@test alphasat(⊥, ∧(α, ⊤), Ł4) == true
@test alphasat(⊥, ∧(β, ⊥), Ł4) == true
@test alphasat(⊥, ∧(β, α), Ł4) == true
@test alphasat(⊥, ∧(β, β), Ł4) == true
@test alphasat(⊥, ∧(β, ⊤), Ł4) == true
@test alphasat(⊥, ∧(⊤, ⊥), Ł4) == true
@test alphasat(⊥, ∧(⊤, α), Ł4) == true
@test alphasat(⊥, ∧(⊤, β), Ł4) == true
@test alphasat(⊥, ∧(⊤, ⊤), Ł4) == true

@test alphasat(α, ∧(⊥, ⊥), Ł4) == false
@test alphasat(α, ∧(⊥, α), Ł4) == false
@test alphasat(α, ∧(⊥, β), Ł4) == false
@test alphasat(α, ∧(⊥, ⊤), Ł4) == false
@test alphasat(α, ∧(α, ⊥), Ł4) == false
@test alphasat(α, ∧(α, α), Ł4) == false
@test alphasat(α, ∧(α, β), Ł4) == false
@test alphasat(α, ∧(α, ⊤), Ł4) == true
@test alphasat(α, ∧(β, ⊥), Ł4) == false
@test alphasat(α, ∧(β, α), Ł4) == false
@test alphasat(α, ∧(β, β), Ł4) == true
@test alphasat(α, ∧(β, ⊤), Ł4) == true
@test alphasat(α, ∧(⊤, ⊥), Ł4) == false
@test alphasat(α, ∧(⊤, α), Ł4) == true
@test alphasat(α, ∧(⊤, β), Ł4) == true
@test alphasat(α, ∧(⊤, ⊤), Ł4) == true

@test alphasat(β, ∧(⊥, ⊥), Ł4) == false
@test alphasat(β, ∧(⊥, α), Ł4) == false
@test alphasat(β, ∧(⊥, β), Ł4) == false
@test alphasat(β, ∧(⊥, ⊤), Ł4) == false
@test alphasat(β, ∧(α, ⊥), Ł4) == false
@test alphasat(β, ∧(α, α), Ł4) == false
@test alphasat(β, ∧(α, β), Ł4) == false
@test alphasat(β, ∧(α, ⊤), Ł4) == false
@test alphasat(β, ∧(β, ⊥), Ł4) == false
@test alphasat(β, ∧(β, α), Ł4) == false
@test alphasat(β, ∧(β, β), Ł4) == false
@test alphasat(β, ∧(β, ⊤), Ł4) == true
@test alphasat(β, ∧(⊤, ⊥), Ł4) == false
@test alphasat(β, ∧(⊤, α), Ł4) == false
@test alphasat(β, ∧(⊤, β), Ł4) == true
@test alphasat(β, ∧(⊤, ⊤), Ł4) == true

@test alphasat(⊤, ∧(⊥, ⊥), Ł4) == false
@test alphasat(⊤, ∧(⊥, α), Ł4) == false
@test alphasat(⊤, ∧(⊥, β), Ł4) == false
@test alphasat(⊤, ∧(⊥, ⊤), Ł4) == false
@test alphasat(⊤, ∧(α, ⊥), Ł4) == false
@test alphasat(⊤, ∧(α, α), Ł4) == false
@test alphasat(⊤, ∧(α, β), Ł4) == false
@test alphasat(⊤, ∧(α, ⊤), Ł4) == false
@test alphasat(⊤, ∧(β, ⊥), Ł4) == false
@test alphasat(⊤, ∧(β, α), Ł4) == false
@test alphasat(⊤, ∧(β, β), Ł4) == false
@test alphasat(⊤, ∧(β, ⊤), Ł4) == false
@test alphasat(⊤, ∧(⊤, ⊥), Ł4) == false
@test alphasat(⊤, ∧(⊤, α), Ł4) == false
@test alphasat(⊤, ∧(⊤, β), Ł4) == false
@test alphasat(⊤, ∧(⊤, ⊤), Ł4) == true

@test alphasat(⊥, ∧(parseformula("p"), ⊥), Ł4) == true
@test alphasat(⊥, ∧(parseformula("p"), α), Ł4) == true
@test alphasat(⊥, ∧(parseformula("p"), β), Ł4) == true
@test alphasat(⊥, ∧(parseformula("p"), ⊤), Ł4) == true
@test alphasat(α, ∧(parseformula("p"), ⊥), Ł4) == false
@test alphasat(α, ∧(parseformula("p"), α), Ł4) == true
@test alphasat(α, ∧(parseformula("p"), β), Ł4) == true
@test alphasat(α, ∧(parseformula("p"), ⊤), Ł4) == true
@test alphasat(β, ∧(parseformula("p"), ⊥), Ł4) == false
@test alphasat(β, ∧(parseformula("p"), α), Ł4) == false
@test alphasat(β, ∧(parseformula("p"), β), Ł4) == true
@test alphasat(β, ∧(parseformula("p"), ⊤), Ł4) == true
@test alphasat(⊤, ∧(parseformula("p"), ⊥), Ł4) == false
@test alphasat(⊤, ∧(parseformula("p"), α), Ł4) == false
@test alphasat(⊤, ∧(parseformula("p"), β), Ł4) == false
@test alphasat(⊤, ∧(parseformula("p"), ⊤), Ł4) == true

@test alphasat(⊥, ∧(⊥, parseformula("p")), Ł4) == true
@test alphasat(⊥, ∧(α, parseformula("p")), Ł4) == true
@test alphasat(⊥, ∧(β, parseformula("p")), Ł4) == true
@test alphasat(⊥, ∧(⊤, parseformula("p")), Ł4) == true
@test alphasat(α, ∧(⊥, parseformula("p")), Ł4) == false
@test alphasat(α, ∧(α, parseformula("p")), Ł4) == true
@test alphasat(α, ∧(β, parseformula("p")), Ł4) == true
@test alphasat(α, ∧(⊤, parseformula("p")), Ł4) == true
@test alphasat(β, ∧(⊥, parseformula("p")), Ł4) == false
@test alphasat(β, ∧(α, parseformula("p")), Ł4) == false
@test alphasat(β, ∧(β, parseformula("p")), Ł4) == true
@test alphasat(β, ∧(⊤, parseformula("p")), Ł4) == true
@test alphasat(⊤, ∧(⊥, parseformula("p")), Ł4) == false
@test alphasat(⊤, ∧(α, parseformula("p")), Ł4) == false
@test alphasat(⊤, ∧(β, parseformula("p")), Ł4) == false
@test alphasat(⊤, ∧(⊤, parseformula("p")), Ł4) == true

@test alphasat(⊥, ∧(parseformula("p"), parseformula("p")), Ł4) == true
@test alphasat(α, ∧(parseformula("p"), parseformula("p")), Ł4) == true
@test alphasat(β, ∧(parseformula("p"), parseformula("p")), Ł4) == true
@test alphasat(⊤, ∧(parseformula("p"), parseformula("p")), Ł4) == true

@test alphasat(⊥, ∧(parseformula("p"), parseformula("q")), Ł4) == true
@test alphasat(α, ∧(parseformula("p"), parseformula("q")), Ł4) == true
@test alphasat(β, ∧(parseformula("p"), parseformula("q")), Ł4) == true
@test alphasat(⊤, ∧(parseformula("p"), parseformula("q")), Ł4) == true

@test alphasat(⊥, ∧(parseformula("q"), parseformula("p")), Ł4) == true
@test alphasat(α, ∧(parseformula("q"), parseformula("p")), Ł4) == true
@test alphasat(β, ∧(parseformula("q"), parseformula("p")), Ł4) == true
@test alphasat(⊤, ∧(parseformula("q"), parseformula("p")), Ł4) == true

############################################################################################
## Implication #############################################################################
############################################################################################

@test alphasat(⊥, →(⊥, ⊥), Ł4) == true
@test alphasat(⊥, →(⊥, α), Ł4) == true
@test alphasat(⊥, →(⊥, β), Ł4) == true
@test alphasat(⊥, →(⊥, ⊤), Ł4) == true
@test alphasat(⊥, →(α, ⊥), Ł4) == true
@test alphasat(⊥, →(α, α), Ł4) == true
@test alphasat(⊥, →(α, β), Ł4) == true
@test alphasat(⊥, →(α, ⊤), Ł4) == true
@test alphasat(⊥, →(β, ⊥), Ł4) == true
@test alphasat(⊥, →(β, α), Ł4) == true
@test alphasat(⊥, →(β, β), Ł4) == true
@test alphasat(⊥, →(β, ⊤), Ł4) == true
@test alphasat(⊥, →(⊤, ⊥), Ł4) == true
@test alphasat(⊥, →(⊤, α), Ł4) == true
@test alphasat(⊥, →(⊤, β), Ł4) == true
@test alphasat(⊥, →(⊤, ⊤), Ł4) == true

@test alphasat(α, →(⊥, ⊥), Ł4) == true
@test alphasat(α, →(⊥, α), Ł4) == true
@test alphasat(α, →(⊥, β), Ł4) == true
@test alphasat(α, →(⊥, ⊤), Ł4) == true
@test alphasat(α, →(α, ⊥), Ł4) == true
@test alphasat(α, →(α, α), Ł4) == true
@test alphasat(α, →(α, β), Ł4) == true
@test alphasat(α, →(α, ⊤), Ł4) == true
@test alphasat(α, →(β, ⊥), Ł4) == true
@test alphasat(α, →(β, α), Ł4) == true
@test alphasat(α, →(β, β), Ł4) == true
@test alphasat(α, →(β, ⊤), Ł4) == true
@test alphasat(α, →(⊤, ⊥), Ł4) == false
@test alphasat(α, →(⊤, α), Ł4) == true
@test alphasat(α, →(⊤, β), Ł4) == true
@test alphasat(α, →(⊤, ⊤), Ł4) == true

@test alphasat(β, →(⊥, ⊥), Ł4) == true
@test alphasat(β, →(⊥, α), Ł4) == true
@test alphasat(β, →(⊥, β), Ł4) == true
@test alphasat(β, →(⊥, ⊤), Ł4) == true
@test alphasat(β, →(α, ⊥), Ł4) == true
@test alphasat(β, →(α, α), Ł4) == true
@test alphasat(β, →(α, β), Ł4) == true
@test alphasat(β, →(α, ⊤), Ł4) == true
@test alphasat(β, →(β, ⊥), Ł4) == false
@test alphasat(β, →(β, α), Ł4) == true
@test alphasat(β, →(β, β), Ł4) == true
@test alphasat(β, →(β, ⊤), Ł4) == true
@test alphasat(β, →(⊤, ⊥), Ł4) == false
@test alphasat(β, →(⊤, α), Ł4) == false
@test alphasat(β, →(⊤, β), Ł4) == true
@test alphasat(β, →(⊤, ⊤), Ł4) == true

@test alphasat(⊤, →(⊥, ⊥), Ł4) == true
@test alphasat(⊤, →(⊥, α), Ł4) == true
@test alphasat(⊤, →(⊥, β), Ł4) == true
@test alphasat(⊤, →(⊥, ⊤), Ł4) == true
@test alphasat(⊤, →(α, ⊥), Ł4) == false
@test alphasat(⊤, →(α, α), Ł4) == true
@test alphasat(⊤, →(α, β), Ł4) == true
@test alphasat(⊤, →(α, ⊤), Ł4) == true
@test alphasat(⊤, →(β, ⊥), Ł4) == false
@test alphasat(⊤, →(β, α), Ł4) == false
@test alphasat(⊤, →(β, β), Ł4) == true
@test alphasat(⊤, →(β, ⊤), Ł4) == true
@test alphasat(⊤, →(⊤, ⊥), Ł4) == false
@test alphasat(⊤, →(⊤, α), Ł4) == false
@test alphasat(⊤, →(⊤, β), Ł4) == false
@test alphasat(⊤, →(⊤, ⊤), Ł4) == true

@test alphasat(⊥, →(parseformula("p"), ⊥), G4) == true
@test alphasat(⊥, →(parseformula("p"), α), G4) == true
@test alphasat(⊥, →(parseformula("p"), β), G4) == true
@test alphasat(⊥, →(parseformula("p"), ⊤), G4) == true
@test alphasat(α, →(parseformula("p"), ⊥), G4) == true
@test alphasat(α, →(parseformula("p"), α), G4) == true
@test alphasat(α, →(parseformula("p"), β), G4) == true
@test alphasat(α, →(parseformula("p"), ⊤), G4) == true
@test alphasat(β, →(parseformula("p"), ⊥), G4) == true
@test alphasat(β, →(parseformula("p"), α), G4) == true
@test alphasat(β, →(parseformula("p"), β), G4) == true
@test alphasat(β, →(parseformula("p"), ⊤), G4) == true
@test alphasat(⊤, →(parseformula("p"), ⊥), G4) == true
@test alphasat(⊤, →(parseformula("p"), α), G4) == true
@test alphasat(⊤, →(parseformula("p"), β), G4) == true
@test alphasat(⊤, →(parseformula("p"), ⊤), G4) == true

@test alphasat(⊥, →(⊥, parseformula("p")), G4) == true
@test alphasat(⊥, →(α, parseformula("p")), G4) == true
@test alphasat(⊥, →(β, parseformula("p")), G4) == true
@test alphasat(⊥, →(⊤, parseformula("p")), G4) == true
@test alphasat(α, →(⊥, parseformula("p")), G4) == true
@test alphasat(α, →(α, parseformula("p")), G4) == true
@test alphasat(α, →(β, parseformula("p")), G4) == true
@test alphasat(α, →(⊤, parseformula("p")), G4) == true
@test alphasat(β, →(⊥, parseformula("p")), G4) == true
@test alphasat(β, →(α, parseformula("p")), G4) == true
@test alphasat(β, →(β, parseformula("p")), G4) == true
@test alphasat(β, →(⊤, parseformula("p")), G4) == true
@test alphasat(⊤, →(⊥, parseformula("p")), G4) == true
@test alphasat(⊤, →(α, parseformula("p")), G4) == true
@test alphasat(⊤, →(β, parseformula("p")), G4) == true
@test alphasat(⊤, →(⊤, parseformula("p")), G4) == true

@test alphasat(⊥, →(parseformula("p"), parseformula("p")), G4) == true
@test alphasat(α, →(parseformula("p"), parseformula("p")), G4) == true
@test alphasat(β, →(parseformula("p"), parseformula("p")), G4) == true
@test alphasat(⊤, →(parseformula("p"), parseformula("p")), G4) == true

@test alphasat(⊥, →(parseformula("p"), parseformula("q")), G4) == true
@test alphasat(α, →(parseformula("p"), parseformula("q")), G4) == true
@test alphasat(β, →(parseformula("p"), parseformula("q")), G4) == true
@test alphasat(⊤, →(parseformula("p"), parseformula("q")), G4) == true

@test alphasat(⊥, →(parseformula("q"), parseformula("p")), G4) == true
@test alphasat(α, →(parseformula("q"), parseformula("p")), G4) == true
@test alphasat(β, →(parseformula("q"), parseformula("p")), G4) == true
@test alphasat(⊤, →(parseformula("q"), parseformula("p")), G4) == true

############################################################################################
#### H4 ####################################################################################
############################################################################################

include("algebras/h4.jl")

############################################################################################
## Base cases ##############################################################################
############################################################################################

@test alphasat(⊥, ⊥, H4) == true
@test alphasat(⊥, α, H4) == true
@test alphasat(⊥, β, H4) == true
@test alphasat(⊥, ⊤, H4) == true
@test alphasat(α, ⊥, H4) == false
@test alphasat(α, α, H4) == true
@test alphasat(α, β, H4) == false
@test alphasat(α, ⊤, H4) == true
@test alphasat(β, ⊥, H4) == false
@test alphasat(β, α, H4) == false
@test alphasat(β, β, H4) == true
@test alphasat(β, ⊤, H4) == true
@test alphasat(⊤, ⊥, H4) == false
@test alphasat(⊤, α, H4) == false
@test alphasat(⊤, β, H4) == false
@test alphasat(⊤, ⊤, H4) == true

@test alphasat(⊥, parseformula("p"), H4) == true
@test alphasat(α, parseformula("p"), H4) == true
@test alphasat(β, parseformula("p"), H4) == true
@test alphasat(⊤, parseformula("p"), H4) == true

############################################################################################
## (Strong) disjuction #####################################################################
############################################################################################

@test alphasat(⊥, ∨(⊥, ⊥), H4) == true
@test alphasat(⊥, ∨(⊥, α), H4) == true
@test alphasat(⊥, ∨(⊥, β), H4) == true
@test alphasat(⊥, ∨(⊥, ⊤), H4) == true
@test alphasat(⊥, ∨(α, ⊥), H4) == true
@test alphasat(⊥, ∨(α, α), H4) == true
@test alphasat(⊥, ∨(α, β), H4) == true
@test alphasat(⊥, ∨(α, ⊤), H4) == true
@test alphasat(⊥, ∨(β, ⊥), H4) == true
@test alphasat(⊥, ∨(β, α), H4) == true
@test alphasat(⊥, ∨(β, β), H4) == true
@test alphasat(⊥, ∨(β, ⊤), H4) == true
@test alphasat(⊥, ∨(⊤, ⊥), H4) == true
@test alphasat(⊥, ∨(⊤, α), H4) == true
@test alphasat(⊥, ∨(⊤, β), H4) == true
@test alphasat(⊥, ∨(⊤, ⊤), H4) == true

@test alphasat(α, ∨(⊥, ⊥), H4) == false
@test alphasat(α, ∨(⊥, α), H4) == true
@test alphasat(α, ∨(⊥, β), H4) == false
@test alphasat(α, ∨(⊥, ⊤), H4) == true
@test alphasat(α, ∨(α, ⊥), H4) == true
@test alphasat(α, ∨(α, α), H4) == true
@test alphasat(α, ∨(α, β), H4) == true
@test alphasat(α, ∨(α, ⊤), H4) == true
@test alphasat(α, ∨(β, ⊥), H4) == false
@test alphasat(α, ∨(β, α), H4) == true
@test alphasat(α, ∨(β, β), H4) == false
@test alphasat(α, ∨(β, ⊤), H4) == true
@test alphasat(α, ∨(⊤, ⊥), H4) == true
@test alphasat(α, ∨(⊤, α), H4) == true
@test alphasat(α, ∨(⊤, β), H4) == true
@test alphasat(α, ∨(⊤, ⊤), H4) == true

@test alphasat(β, ∨(⊥, ⊥), H4) == false
@test alphasat(β, ∨(⊥, α), H4) == false
@test alphasat(β, ∨(⊥, β), H4) == true
@test alphasat(β, ∨(⊥, ⊤), H4) == true
@test alphasat(β, ∨(α, ⊥), H4) == false
@test alphasat(β, ∨(α, α), H4) == false
@test alphasat(β, ∨(α, β), H4) == true
@test alphasat(β, ∨(α, ⊤), H4) == true
@test alphasat(β, ∨(β, ⊥), H4) == true
@test alphasat(β, ∨(β, α), H4) == true
@test alphasat(β, ∨(β, β), H4) == true
@test alphasat(β, ∨(β, ⊤), H4) == true
@test alphasat(β, ∨(⊤, ⊥), H4) == true
@test alphasat(β, ∨(⊤, α), H4) == true
@test alphasat(β, ∨(⊤, β), H4) == true
@test alphasat(β, ∨(⊤, ⊤), H4) == true

@test alphasat(⊤, ∨(⊥, ⊥), H4) == false
@test alphasat(⊤, ∨(⊥, α), H4) == false
@test alphasat(⊤, ∨(⊥, β), H4) == false
@test alphasat(⊤, ∨(⊥, ⊤), H4) == true
@test alphasat(⊤, ∨(α, ⊥), H4) == false
@test alphasat(⊤, ∨(α, α), H4) == false
@test alphasat(⊤, ∨(α, β), H4) == true
@test alphasat(⊤, ∨(α, ⊤), H4) == true
@test alphasat(⊤, ∨(β, ⊥), H4) == false
@test alphasat(⊤, ∨(β, α), H4) == true
@test alphasat(⊤, ∨(β, β), H4) == false
@test alphasat(⊤, ∨(β, ⊤), H4) == true
@test alphasat(⊤, ∨(⊤, ⊥), H4) == true
@test alphasat(⊤, ∨(⊤, α), H4) == true
@test alphasat(⊤, ∨(⊤, β), H4) == true
@test alphasat(⊤, ∨(⊤, ⊤), H4) == true

@test alphasat(⊥, ∨(parseformula("p"), ⊥), H4) == true
@test alphasat(⊥, ∨(parseformula("p"), α), H4) == true
@test alphasat(⊥, ∨(parseformula("p"), β), H4) == true
@test alphasat(⊥, ∨(parseformula("p"), ⊤), H4) == true
@test alphasat(α, ∨(parseformula("p"), ⊥), H4) == true
@test alphasat(α, ∨(parseformula("p"), α), H4) == true
@test alphasat(α, ∨(parseformula("p"), β), H4) == true
@test alphasat(α, ∨(parseformula("p"), ⊤), H4) == true
@test alphasat(β, ∨(parseformula("p"), ⊥), H4) == true
@test alphasat(β, ∨(parseformula("p"), α), H4) == true
@test alphasat(β, ∨(parseformula("p"), β), H4) == true
@test alphasat(β, ∨(parseformula("p"), ⊤), H4) == true
@test alphasat(⊤, ∨(parseformula("p"), ⊥), H4) == true
@test alphasat(⊤, ∨(parseformula("p"), α), H4) == true
@test alphasat(⊤, ∨(parseformula("p"), β), H4) == true
@test alphasat(⊤, ∨(parseformula("p"), ⊤), H4) == true

@test alphasat(⊥, ∨(⊥, parseformula("p")), H4) == true
@test alphasat(⊥, ∨(α, parseformula("p")), H4) == true
@test alphasat(⊥, ∨(β, parseformula("p")), H4) == true
@test alphasat(⊥, ∨(⊤, parseformula("p")), H4) == true
@test alphasat(α, ∨(⊥, parseformula("p")), H4) == true
@test alphasat(α, ∨(α, parseformula("p")), H4) == true
@test alphasat(α, ∨(β, parseformula("p")), H4) == true
@test alphasat(α, ∨(⊤, parseformula("p")), H4) == true
@test alphasat(β, ∨(⊥, parseformula("p")), H4) == true
@test alphasat(β, ∨(α, parseformula("p")), H4) == true
@test alphasat(β, ∨(β, parseformula("p")), H4) == true
@test alphasat(β, ∨(⊤, parseformula("p")), H4) == true
@test alphasat(⊤, ∨(⊥, parseformula("p")), H4) == true
@test alphasat(⊤, ∨(α, parseformula("p")), H4) == true
@test alphasat(⊤, ∨(β, parseformula("p")), H4) == true
@test alphasat(⊤, ∨(⊤, parseformula("p")), H4) == true

@test alphasat(⊥, ∨(parseformula("p"), parseformula("p")), H4) == true
@test alphasat(α, ∨(parseformula("p"), parseformula("p")), H4) == true
@test alphasat(β, ∨(parseformula("p"), parseformula("p")), H4) == true
@test alphasat(⊤, ∨(parseformula("p"), parseformula("p")), H4) == true

@test alphasat(⊥, ∨(parseformula("p"), parseformula("q")), H4) == true
@test alphasat(α, ∨(parseformula("p"), parseformula("q")), H4) == true
@test alphasat(β, ∨(parseformula("p"), parseformula("q")), H4) == true
@test alphasat(⊤, ∨(parseformula("p"), parseformula("q")), H4) == true

@test alphasat(⊥, ∨(parseformula("q"), parseformula("q")), H4) == true
@test alphasat(α, ∨(parseformula("q"), parseformula("q")), H4) == true
@test alphasat(β, ∨(parseformula("q"), parseformula("q")), H4) == true
@test alphasat(⊤, ∨(parseformula("q"), parseformula("q")), H4) == true

############################################################################################
## (Strong) conjunction ####################################################################
############################################################################################

@test alphasat(⊥, ∧(⊥, ⊥), H4) == true
@test alphasat(⊥, ∧(⊥, α), H4) == true
@test alphasat(⊥, ∧(⊥, β), H4) == true
@test alphasat(⊥, ∧(⊥, ⊤), H4) == true
@test alphasat(⊥, ∧(α, ⊥), H4) == true
@test alphasat(⊥, ∧(α, α), H4) == true
@test alphasat(⊥, ∧(α, β), H4) == true
@test alphasat(⊥, ∧(α, ⊤), H4) == true
@test alphasat(⊥, ∧(β, ⊥), H4) == true
@test alphasat(⊥, ∧(β, α), H4) == true
@test alphasat(⊥, ∧(β, β), H4) == true
@test alphasat(⊥, ∧(β, ⊤), H4) == true
@test alphasat(⊥, ∧(⊤, ⊥), H4) == true
@test alphasat(⊥, ∧(⊤, α), H4) == true
@test alphasat(⊥, ∧(⊤, β), H4) == true
@test alphasat(⊥, ∧(⊤, ⊤), H4) == true

@test alphasat(α, ∧(⊥, ⊥), H4) == false
@test alphasat(α, ∧(⊥, α), H4) == false
@test alphasat(α, ∧(⊥, β), H4) == false
@test alphasat(α, ∧(⊥, ⊤), H4) == false
@test alphasat(α, ∧(α, ⊥), H4) == false
@test alphasat(α, ∧(α, α), H4) == true
@test alphasat(α, ∧(α, β), H4) == false
@test alphasat(α, ∧(α, ⊤), H4) == true
@test alphasat(α, ∧(β, ⊥), H4) == false
@test alphasat(α, ∧(β, α), H4) == false
@test alphasat(α, ∧(β, β), H4) == false
@test alphasat(α, ∧(β, ⊤), H4) == false
@test alphasat(α, ∧(⊤, ⊥), H4) == false
@test alphasat(α, ∧(⊤, α), H4) == true
@test alphasat(α, ∧(⊤, β), H4) == false
@test alphasat(α, ∧(⊤, ⊤), H4) == true

@test alphasat(β, ∧(⊥, ⊥), H4) == false
@test alphasat(β, ∧(⊥, α), H4) == false
@test alphasat(β, ∧(⊥, β), H4) == false
@test alphasat(β, ∧(⊥, ⊤), H4) == false
@test alphasat(β, ∧(α, ⊥), H4) == false
@test alphasat(β, ∧(α, α), H4) == false
@test alphasat(β, ∧(α, β), H4) == false
@test alphasat(β, ∧(α, ⊤), H4) == false
@test alphasat(β, ∧(β, ⊥), H4) == false
@test alphasat(β, ∧(β, α), H4) == false
@test alphasat(β, ∧(β, β), H4) == true
@test alphasat(β, ∧(β, ⊤), H4) == true
@test alphasat(β, ∧(⊤, ⊥), H4) == false
@test alphasat(β, ∧(⊤, α), H4) == false
@test alphasat(β, ∧(⊤, β), H4) == true
@test alphasat(β, ∧(⊤, ⊤), H4) == true

@test alphasat(⊤, ∧(⊥, ⊥), H4) == false
@test alphasat(⊤, ∧(⊥, α), H4) == false
@test alphasat(⊤, ∧(⊥, β), H4) == false
@test alphasat(⊤, ∧(⊥, ⊤), H4) == false
@test alphasat(⊤, ∧(α, ⊥), H4) == false
@test alphasat(⊤, ∧(α, α), H4) == false
@test alphasat(⊤, ∧(α, β), H4) == false
@test alphasat(⊤, ∧(α, ⊤), H4) == false
@test alphasat(⊤, ∧(β, ⊥), H4) == false
@test alphasat(⊤, ∧(β, α), H4) == false
@test alphasat(⊤, ∧(β, β), H4) == false
@test alphasat(⊤, ∧(β, ⊤), H4) == false
@test alphasat(⊤, ∧(⊤, ⊥), H4) == false
@test alphasat(⊤, ∧(⊤, α), H4) == false
@test alphasat(⊤, ∧(⊤, β), H4) == false
@test alphasat(⊤, ∧(⊤, ⊤), H4) == true

@test alphasat(⊥, ∧(parseformula("p"), ⊥), H4) == true
@test alphasat(⊥, ∧(parseformula("p"), α), H4) == true
@test alphasat(⊥, ∧(parseformula("p"), β), H4) == true
@test alphasat(⊥, ∧(parseformula("p"), ⊤), H4) == true
@test alphasat(α, ∧(parseformula("p"), ⊥), H4) == false
@test alphasat(α, ∧(parseformula("p"), α), H4) == true
@test alphasat(α, ∧(parseformula("p"), β), H4) == false
@test alphasat(α, ∧(parseformula("p"), ⊤), H4) == true
@test alphasat(β, ∧(parseformula("p"), ⊥), H4) == false
@test alphasat(β, ∧(parseformula("p"), α), H4) == false
@test alphasat(β, ∧(parseformula("p"), β), H4) == true
@test alphasat(β, ∧(parseformula("p"), ⊤), H4) == true
@test alphasat(⊤, ∧(parseformula("p"), ⊥), H4) == false
@test alphasat(⊤, ∧(parseformula("p"), α), H4) == false
@test alphasat(⊤, ∧(parseformula("p"), β), H4) == false
@test alphasat(⊤, ∧(parseformula("p"), ⊤), H4) == true

@test alphasat(⊥, ∧(⊥, parseformula("p")), H4) == true
@test alphasat(⊥, ∧(α, parseformula("p")), H4) == true
@test alphasat(⊥, ∧(β, parseformula("p")), H4) == true
@test alphasat(⊥, ∧(⊤, parseformula("p")), H4) == true
@test alphasat(α, ∧(⊥, parseformula("p")), H4) == false
@test alphasat(α, ∧(α, parseformula("p")), H4) == true
@test alphasat(α, ∧(β, parseformula("p")), H4) == false
@test alphasat(α, ∧(⊤, parseformula("p")), H4) == true
@test alphasat(β, ∧(⊥, parseformula("p")), H4) == false
@test alphasat(β, ∧(α, parseformula("p")), H4) == false
@test alphasat(β, ∧(β, parseformula("p")), H4) == true
@test alphasat(β, ∧(⊤, parseformula("p")), H4) == true
@test alphasat(⊤, ∧(⊥, parseformula("p")), H4) == false
@test alphasat(⊤, ∧(α, parseformula("p")), H4) == false
@test alphasat(⊤, ∧(β, parseformula("p")), H4) == false
@test alphasat(⊤, ∧(⊤, parseformula("p")), H4) == true

@test alphasat(⊥, ∧(parseformula("p"), parseformula("p")), H4) == true
@test alphasat(α, ∧(parseformula("p"), parseformula("p")), H4) == true
@test alphasat(β, ∧(parseformula("p"), parseformula("p")), H4) == true
@test alphasat(⊤, ∧(parseformula("p"), parseformula("p")), H4) == true

@test alphasat(⊥, ∧(parseformula("p"), parseformula("q")), H4) == true
@test alphasat(α, ∧(parseformula("p"), parseformula("q")), H4) == true
@test alphasat(β, ∧(parseformula("p"), parseformula("q")), H4) == true
@test alphasat(⊤, ∧(parseformula("p"), parseformula("q")), H4) == true

@test alphasat(⊥, ∧(parseformula("q"), parseformula("p")), H4) == true
@test alphasat(α, ∧(parseformula("q"), parseformula("p")), H4) == true
@test alphasat(β, ∧(parseformula("q"), parseformula("p")), H4) == true
@test alphasat(⊤, ∧(parseformula("q"), parseformula("p")), H4) == true

############################################################################################
## Implication #############################################################################
############################################################################################

@test alphasat(⊥, →(⊥, ⊥), H4) == true
@test alphasat(⊥, →(⊥, α), H4) == true
@test alphasat(⊥, →(⊥, β), H4) == true
@test alphasat(⊥, →(⊥, ⊤), H4) == true
@test alphasat(⊥, →(α, ⊥), H4) == true
@test alphasat(⊥, →(α, α), H4) == true
@test alphasat(⊥, →(α, β), H4) == true
@test alphasat(⊥, →(α, ⊤), H4) == true
@test alphasat(⊥, →(β, ⊥), H4) == true
@test alphasat(⊥, →(β, α), H4) == true
@test alphasat(⊥, →(β, β), H4) == true
@test alphasat(⊥, →(β, ⊤), H4) == true
@test alphasat(⊥, →(⊤, ⊥), H4) == true
@test alphasat(⊥, →(⊤, α), H4) == true
@test alphasat(⊥, →(⊤, β), H4) == true
@test alphasat(⊥, →(⊤, ⊤), H4) == true

@test alphasat(α, →(⊥, ⊥), H4) == true
@test alphasat(α, →(⊥, α), H4) == true
@test alphasat(α, →(⊥, β), H4) == true
@test alphasat(α, →(⊥, ⊤), H4) == true
@test alphasat(α, →(α, ⊥), H4) == false
@test alphasat(α, →(α, α), H4) == true
@test alphasat(α, →(α, β), H4) == false
@test alphasat(α, →(α, ⊤), H4) == true
@test alphasat(α, →(β, ⊥), H4) == true
@test alphasat(α, →(β, α), H4) == true
@test alphasat(α, →(β, β), H4) == true
@test alphasat(α, →(β, ⊤), H4) == true
@test alphasat(α, →(⊤, ⊥), H4) == false
@test alphasat(α, →(⊤, α), H4) == true
@test alphasat(α, →(⊤, β), H4) == false
@test alphasat(α, →(⊤, ⊤), H4) == true

@test alphasat(β, →(⊥, ⊥), H4) == true
@test alphasat(β, →(⊥, α), H4) == true
@test alphasat(β, →(⊥, β), H4) == true
@test alphasat(β, →(⊥, ⊤), H4) == true
@test alphasat(β, →(α, ⊥), H4) == true
@test alphasat(β, →(α, α), H4) == true
@test alphasat(β, →(α, β), H4) == true
@test alphasat(β, →(α, ⊤), H4) == true
@test alphasat(β, →(β, ⊥), H4) == false
@test alphasat(β, →(β, α), H4) == false
@test alphasat(β, →(β, β), H4) == true
@test alphasat(β, →(β, ⊤), H4) == true
@test alphasat(β, →(⊤, ⊥), H4) == false
@test alphasat(β, →(⊤, α), H4) == false
@test alphasat(β, →(⊤, β), H4) == true
@test alphasat(β, →(⊤, ⊤), H4) == true

@test alphasat(⊤, →(⊥, ⊥), H4) == true
@test alphasat(⊤, →(⊥, α), H4) == true
@test alphasat(⊤, →(⊥, β), H4) == true
@test alphasat(⊤, →(⊥, ⊤), H4) == true
@test alphasat(⊤, →(α, ⊥), H4) == false
@test alphasat(⊤, →(α, α), H4) == true
@test alphasat(⊤, →(α, β), H4) == false
@test alphasat(⊤, →(α, ⊤), H4) == true
@test alphasat(⊤, →(β, ⊥), H4) == false
@test alphasat(⊤, →(β, α), H4) == false
@test alphasat(⊤, →(β, β), H4) == true
@test alphasat(⊤, →(β, ⊤), H4) == true
@test alphasat(⊤, →(⊤, ⊥), H4) == false
@test alphasat(⊤, →(⊤, α), H4) == false
@test alphasat(⊤, →(⊤, β), H4) == false
@test alphasat(⊤, →(⊤, ⊤), H4) == true

@test alphasat(⊥, →(parseformula("p"), ⊥), H4) == true
@test alphasat(⊥, →(parseformula("p"), α), H4) == true
@test alphasat(⊥, →(parseformula("p"), β), H4) == true
@test alphasat(⊥, →(parseformula("p"), ⊤), H4) == true
@test alphasat(α, →(parseformula("p"), ⊥), H4) == true
@test alphasat(α, →(parseformula("p"), α), H4) == true
@test alphasat(α, →(parseformula("p"), β), H4) == true
@test alphasat(α, →(parseformula("p"), ⊤), H4) == true
@test alphasat(β, →(parseformula("p"), ⊥), H4) == true
@test alphasat(β, →(parseformula("p"), α), H4) == true
@test alphasat(β, →(parseformula("p"), β), H4) == true
@test alphasat(β, →(parseformula("p"), ⊤), H4) == true
@test alphasat(⊤, →(parseformula("p"), ⊥), H4) == true
@test alphasat(⊤, →(parseformula("p"), α), H4) == true
@test alphasat(⊤, →(parseformula("p"), β), H4) == true
@test alphasat(⊤, →(parseformula("p"), ⊤), H4) == true

@test alphasat(⊥, →(⊥, parseformula("p")), H4) == true
@test alphasat(⊥, →(α, parseformula("p")), H4) == true
@test alphasat(⊥, →(β, parseformula("p")), H4) == true
@test alphasat(⊥, →(⊤, parseformula("p")), H4) == true
@test alphasat(α, →(⊥, parseformula("p")), H4) == true
@test alphasat(α, →(α, parseformula("p")), H4) == true
@test alphasat(α, →(β, parseformula("p")), H4) == true
@test alphasat(α, →(⊤, parseformula("p")), H4) == true
@test alphasat(β, →(⊥, parseformula("p")), H4) == true
@test alphasat(β, →(α, parseformula("p")), H4) == true
@test alphasat(β, →(β, parseformula("p")), H4) == true
@test alphasat(β, →(⊤, parseformula("p")), H4) == true
@test alphasat(⊤, →(⊥, parseformula("p")), H4) == true
@test alphasat(⊤, →(α, parseformula("p")), H4) == true
@test alphasat(⊤, →(β, parseformula("p")), H4) == true
@test alphasat(⊤, →(⊤, parseformula("p")), H4) == true

@test alphasat(⊥, →(parseformula("p"), parseformula("p")), H4) == true
@test alphasat(α, →(parseformula("p"), parseformula("p")), H4) == true
@test alphasat(β, →(parseformula("p"), parseformula("p")), H4) == true
@test alphasat(⊤, →(parseformula("p"), parseformula("p")), H4) == true

@test alphasat(⊥, →(parseformula("p"), parseformula("q")), H4) == true
@test alphasat(α, →(parseformula("p"), parseformula("q")), H4) == true
@test alphasat(β, →(parseformula("p"), parseformula("q")), H4) == true
@test alphasat(⊤, →(parseformula("p"), parseformula("q")), H4) == true

@test alphasat(⊥, →(parseformula("q"), parseformula("p")), H4) == true
@test alphasat(α, →(parseformula("q"), parseformula("p")), H4) == true
@test alphasat(β, →(parseformula("q"), parseformula("p")), H4) == true
@test alphasat(⊤, →(parseformula("q"), parseformula("p")), H4) == true
