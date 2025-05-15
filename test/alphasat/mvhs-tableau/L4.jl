################################################################################
#### Ł4 ########################################################################
################################################################################

using SoleLogics.ManyValuedLogics: Ł4
using SoleLogics.ManyValuedLogics: α, β

################################################################################
## Base cases ##################################################################
################################################################################

@test alphasat(MVHSTableau, ⊥, ⊥, Ł4) == true
@test alphasat(MVHSTableau, ⊥, α, Ł4) == true
@test alphasat(MVHSTableau, ⊥, β, Ł4) == true
@test alphasat(MVHSTableau, ⊥, ⊤, Ł4) == true
@test alphasat(MVHSTableau, α, ⊥, Ł4) == false
@test alphasat(MVHSTableau, α, α, Ł4) == true
@test alphasat(MVHSTableau, α, β, Ł4) == true
@test alphasat(MVHSTableau, α, ⊤, Ł4) == true
@test alphasat(MVHSTableau, β, ⊥, Ł4) == false
@test alphasat(MVHSTableau, β, α, Ł4) == false
@test alphasat(MVHSTableau, β, β, Ł4) == true
@test alphasat(MVHSTableau, β, ⊤, Ł4) == true
@test alphasat(MVHSTableau, ⊤, ⊥, Ł4) == false
@test alphasat(MVHSTableau, ⊤, α, Ł4) == false
@test alphasat(MVHSTableau, ⊤, β, Ł4) == false
@test alphasat(MVHSTableau, ⊤, ⊤, Ł4) == true

@test alphasat(MVHSTableau, ⊥, parseformula("p"), Ł4) == true
@test alphasat(MVHSTableau, α, parseformula("p"), Ł4) == true
@test alphasat(MVHSTableau, β, parseformula("p"), Ł4) == true
@test alphasat(MVHSTableau, ⊤, parseformula("p"), Ł4) == true

################################################################################
## (Strong) disjuction #########################################################
################################################################################

@test alphasat(MVHSTableau, ⊥, ∨(⊥, ⊥), Ł4) == true
@test alphasat(MVHSTableau, ⊥, ∨(⊥, α), Ł4) == true
@test alphasat(MVHSTableau, ⊥, ∨(⊥, β), Ł4) == true
@test alphasat(MVHSTableau, ⊥, ∨(⊥, ⊤), Ł4) == true
@test alphasat(MVHSTableau, ⊥, ∨(α, ⊥), Ł4) == true
@test alphasat(MVHSTableau, ⊥, ∨(α, α), Ł4) == true
@test alphasat(MVHSTableau, ⊥, ∨(α, β), Ł4) == true
@test alphasat(MVHSTableau, ⊥, ∨(α, ⊤), Ł4) == true
@test alphasat(MVHSTableau, ⊥, ∨(β, ⊥), Ł4) == true
@test alphasat(MVHSTableau, ⊥, ∨(β, α), Ł4) == true
@test alphasat(MVHSTableau, ⊥, ∨(β, β), Ł4) == true
@test alphasat(MVHSTableau, ⊥, ∨(β, ⊤), Ł4) == true
@test alphasat(MVHSTableau, ⊥, ∨(⊤, ⊥), Ł4) == true
@test alphasat(MVHSTableau, ⊥, ∨(⊤, α), Ł4) == true
@test alphasat(MVHSTableau, ⊥, ∨(⊤, β), Ł4) == true
@test alphasat(MVHSTableau, ⊥, ∨(⊤, ⊤), Ł4) == true

@test alphasat(MVHSTableau, α, ∨(⊥, ⊥), Ł4) == false
@test alphasat(MVHSTableau, α, ∨(⊥, α), Ł4) == true
@test alphasat(MVHSTableau, α, ∨(⊥, β), Ł4) == true
@test alphasat(MVHSTableau, α, ∨(⊥, ⊤), Ł4) == true
@test alphasat(MVHSTableau, α, ∨(α, ⊥), Ł4) == true
@test alphasat(MVHSTableau, α, ∨(α, α), Ł4) == true
@test alphasat(MVHSTableau, α, ∨(α, β), Ł4) == true
@test alphasat(MVHSTableau, α, ∨(α, ⊤), Ł4) == true
@test alphasat(MVHSTableau, α, ∨(β, ⊥), Ł4) == true
@test alphasat(MVHSTableau, α, ∨(β, α), Ł4) == true
@test alphasat(MVHSTableau, α, ∨(β, β), Ł4) == true
@test alphasat(MVHSTableau, α, ∨(β, ⊤), Ł4) == true
@test alphasat(MVHSTableau, α, ∨(⊤, ⊥), Ł4) == true
@test alphasat(MVHSTableau, α, ∨(⊤, α), Ł4) == true
@test alphasat(MVHSTableau, α, ∨(⊤, β), Ł4) == true
@test alphasat(MVHSTableau, α, ∨(⊤, ⊤), Ł4) == true

@test alphasat(MVHSTableau, β, ∨(⊥, ⊥), Ł4) == false
@test alphasat(MVHSTableau, β, ∨(⊥, α), Ł4) == false
@test alphasat(MVHSTableau, β, ∨(⊥, β), Ł4) == true
@test alphasat(MVHSTableau, β, ∨(⊥, ⊤), Ł4) == true
@test alphasat(MVHSTableau, β, ∨(α, ⊥), Ł4) == false
@test alphasat(MVHSTableau, β, ∨(α, α), Ł4) == false
@test alphasat(MVHSTableau, β, ∨(α, β), Ł4) == true
@test alphasat(MVHSTableau, β, ∨(α, ⊤), Ł4) == true
@test alphasat(MVHSTableau, β, ∨(β, ⊥), Ł4) == true
@test alphasat(MVHSTableau, β, ∨(β, α), Ł4) == true
@test alphasat(MVHSTableau, β, ∨(β, β), Ł4) == true
@test alphasat(MVHSTableau, β, ∨(β, ⊤), Ł4) == true
@test alphasat(MVHSTableau, β, ∨(⊤, ⊥), Ł4) == true
@test alphasat(MVHSTableau, β, ∨(⊤, α), Ł4) == true
@test alphasat(MVHSTableau, β, ∨(⊤, β), Ł4) == true
@test alphasat(MVHSTableau, β, ∨(⊤, ⊤), Ł4) == true

@test alphasat(MVHSTableau, ⊤, ∨(⊥, ⊥), Ł4) == false
@test alphasat(MVHSTableau, ⊤, ∨(⊥, α), Ł4) == false
@test alphasat(MVHSTableau, ⊤, ∨(⊥, β), Ł4) == false
@test alphasat(MVHSTableau, ⊤, ∨(⊥, ⊤), Ł4) == true
@test alphasat(MVHSTableau, ⊤, ∨(α, ⊥), Ł4) == false
@test alphasat(MVHSTableau, ⊤, ∨(α, α), Ł4) == false
@test alphasat(MVHSTableau, ⊤, ∨(α, β), Ł4) == false
@test alphasat(MVHSTableau, ⊤, ∨(α, ⊤), Ł4) == true
@test alphasat(MVHSTableau, ⊤, ∨(β, ⊥), Ł4) == false
@test alphasat(MVHSTableau, ⊤, ∨(β, α), Ł4) == false
@test alphasat(MVHSTableau, ⊤, ∨(β, β), Ł4) == false
@test alphasat(MVHSTableau, ⊤, ∨(β, ⊤), Ł4) == true
@test alphasat(MVHSTableau, ⊤, ∨(⊤, ⊥), Ł4) == true
@test alphasat(MVHSTableau, ⊤, ∨(⊤, α), Ł4) == true
@test alphasat(MVHSTableau, ⊤, ∨(⊤, β), Ł4) == true
@test alphasat(MVHSTableau, ⊤, ∨(⊤, ⊤), Ł4) == true

@test alphasat(MVHSTableau, ⊥, ∨(parseformula("p"), ⊥), Ł4) == true
@test alphasat(MVHSTableau, ⊥, ∨(parseformula("p"), α), Ł4) == true
@test alphasat(MVHSTableau, ⊥, ∨(parseformula("p"), β), Ł4) == true
@test alphasat(MVHSTableau, ⊥, ∨(parseformula("p"), ⊤), Ł4) == true
@test alphasat(MVHSTableau, α, ∨(parseformula("p"), ⊥), Ł4) == true
@test alphasat(MVHSTableau, α, ∨(parseformula("p"), α), Ł4) == true
@test alphasat(MVHSTableau, α, ∨(parseformula("p"), β), Ł4) == true
@test alphasat(MVHSTableau, α, ∨(parseformula("p"), ⊤), Ł4) == true
@test alphasat(MVHSTableau, β, ∨(parseformula("p"), ⊥), Ł4) == true
@test alphasat(MVHSTableau, β, ∨(parseformula("p"), α), Ł4) == true
@test alphasat(MVHSTableau, β, ∨(parseformula("p"), β), Ł4) == true
@test alphasat(MVHSTableau, β, ∨(parseformula("p"), ⊤), Ł4) == true
@test alphasat(MVHSTableau, ⊤, ∨(parseformula("p"), ⊥), Ł4) == true
@test alphasat(MVHSTableau, ⊤, ∨(parseformula("p"), α), Ł4) == true
@test alphasat(MVHSTableau, ⊤, ∨(parseformula("p"), β), Ł4) == true
@test alphasat(MVHSTableau, ⊤, ∨(parseformula("p"), ⊤), Ł4) == true

@test alphasat(MVHSTableau, ⊥, ∨(⊥, parseformula("p")), Ł4) == true
@test alphasat(MVHSTableau, ⊥, ∨(α, parseformula("p")), Ł4) == true
@test alphasat(MVHSTableau, ⊥, ∨(β, parseformula("p")), Ł4) == true
@test alphasat(MVHSTableau, ⊥, ∨(⊤, parseformula("p")), Ł4) == true
@test alphasat(MVHSTableau, α, ∨(⊥, parseformula("p")), Ł4) == true
@test alphasat(MVHSTableau, α, ∨(α, parseformula("p")), Ł4) == true
@test alphasat(MVHSTableau, α, ∨(β, parseformula("p")), Ł4) == true
@test alphasat(MVHSTableau, α, ∨(⊤, parseformula("p")), Ł4) == true
@test alphasat(MVHSTableau, β, ∨(⊥, parseformula("p")), Ł4) == true
@test alphasat(MVHSTableau, β, ∨(α, parseformula("p")), Ł4) == true
@test alphasat(MVHSTableau, β, ∨(β, parseformula("p")), Ł4) == true
@test alphasat(MVHSTableau, β, ∨(⊤, parseformula("p")), Ł4) == true
@test alphasat(MVHSTableau, ⊤, ∨(⊥, parseformula("p")), Ł4) == true
@test alphasat(MVHSTableau, ⊤, ∨(α, parseformula("p")), Ł4) == true
@test alphasat(MVHSTableau, ⊤, ∨(β, parseformula("p")), Ł4) == true
@test alphasat(MVHSTableau, ⊤, ∨(⊤, parseformula("p")), Ł4) == true

@test alphasat(MVHSTableau, ⊥, ∨(parseformula("p"), parseformula("p")), Ł4)
@test alphasat(MVHSTableau, α, ∨(parseformula("p"), parseformula("p")), Ł4)
@test alphasat(MVHSTableau, β, ∨(parseformula("p"), parseformula("p")), Ł4)
@test alphasat(MVHSTableau, ⊤, ∨(parseformula("p"), parseformula("p")), Ł4)

@test alphasat(MVHSTableau, ⊥, ∨(parseformula("p"), parseformula("q")), Ł4)
@test alphasat(MVHSTableau, α, ∨(parseformula("p"), parseformula("q")), Ł4)
@test alphasat(MVHSTableau, β, ∨(parseformula("p"), parseformula("q")), Ł4)
@test alphasat(MVHSTableau, ⊤, ∨(parseformula("p"), parseformula("q")), Ł4)

@test alphasat(MVHSTableau, ⊥, ∨(parseformula("q"), parseformula("q")), Ł4)
@test alphasat(MVHSTableau, α, ∨(parseformula("q"), parseformula("q")), Ł4)
@test alphasat(MVHSTableau, β, ∨(parseformula("q"), parseformula("q")), Ł4)
@test alphasat(MVHSTableau, ⊤, ∨(parseformula("q"), parseformula("q")), Ł4)

################################################################################
## (Strong) conjunction ########################################################
################################################################################

@test alphasat(MVHSTableau, ⊥, ∧(⊥, ⊥), Ł4) == true
@test alphasat(MVHSTableau, ⊥, ∧(⊥, α), Ł4) == true
@test alphasat(MVHSTableau, ⊥, ∧(⊥, β), Ł4) == true
@test alphasat(MVHSTableau, ⊥, ∧(⊥, ⊤), Ł4) == true
@test alphasat(MVHSTableau, ⊥, ∧(α, ⊥), Ł4) == true
@test alphasat(MVHSTableau, ⊥, ∧(α, α), Ł4) == true
@test alphasat(MVHSTableau, ⊥, ∧(α, β), Ł4) == true
@test alphasat(MVHSTableau, ⊥, ∧(α, ⊤), Ł4) == true
@test alphasat(MVHSTableau, ⊥, ∧(β, ⊥), Ł4) == true
@test alphasat(MVHSTableau, ⊥, ∧(β, α), Ł4) == true
@test alphasat(MVHSTableau, ⊥, ∧(β, β), Ł4) == true
@test alphasat(MVHSTableau, ⊥, ∧(β, ⊤), Ł4) == true
@test alphasat(MVHSTableau, ⊥, ∧(⊤, ⊥), Ł4) == true
@test alphasat(MVHSTableau, ⊥, ∧(⊤, α), Ł4) == true
@test alphasat(MVHSTableau, ⊥, ∧(⊤, β), Ł4) == true
@test alphasat(MVHSTableau, ⊥, ∧(⊤, ⊤), Ł4) == true

@test alphasat(MVHSTableau, α, ∧(⊥, ⊥), Ł4) == false
@test alphasat(MVHSTableau, α, ∧(⊥, α), Ł4) == false
@test alphasat(MVHSTableau, α, ∧(⊥, β), Ł4) == false
@test alphasat(MVHSTableau, α, ∧(⊥, ⊤), Ł4) == false
@test alphasat(MVHSTableau, α, ∧(α, ⊥), Ł4) == false
@test alphasat(MVHSTableau, α, ∧(α, α), Ł4) == false
@test alphasat(MVHSTableau, α, ∧(α, β), Ł4) == false
@test alphasat(MVHSTableau, α, ∧(α, ⊤), Ł4) == true
@test alphasat(MVHSTableau, α, ∧(β, ⊥), Ł4) == false
@test alphasat(MVHSTableau, α, ∧(β, α), Ł4) == false
@test alphasat(MVHSTableau, α, ∧(β, β), Ł4) == true
@test alphasat(MVHSTableau, α, ∧(β, ⊤), Ł4) == true
@test alphasat(MVHSTableau, α, ∧(⊤, ⊥), Ł4) == false
@test alphasat(MVHSTableau, α, ∧(⊤, α), Ł4) == true
@test alphasat(MVHSTableau, α, ∧(⊤, β), Ł4) == true
@test alphasat(MVHSTableau, α, ∧(⊤, ⊤), Ł4) == true

@test alphasat(MVHSTableau, β, ∧(⊥, ⊥), Ł4) == false
@test alphasat(MVHSTableau, β, ∧(⊥, α), Ł4) == false
@test alphasat(MVHSTableau, β, ∧(⊥, β), Ł4) == false
@test alphasat(MVHSTableau, β, ∧(⊥, ⊤), Ł4) == false
@test alphasat(MVHSTableau, β, ∧(α, ⊥), Ł4) == false
@test alphasat(MVHSTableau, β, ∧(α, α), Ł4) == false
@test alphasat(MVHSTableau, β, ∧(α, β), Ł4) == false
@test alphasat(MVHSTableau, β, ∧(α, ⊤), Ł4) == false
@test alphasat(MVHSTableau, β, ∧(β, ⊥), Ł4) == false
@test alphasat(MVHSTableau, β, ∧(β, α), Ł4) == false
@test alphasat(MVHSTableau, β, ∧(β, β), Ł4) == false
@test alphasat(MVHSTableau, β, ∧(β, ⊤), Ł4) == true
@test alphasat(MVHSTableau, β, ∧(⊤, ⊥), Ł4) == false
@test alphasat(MVHSTableau, β, ∧(⊤, α), Ł4) == false
@test alphasat(MVHSTableau, β, ∧(⊤, β), Ł4) == true
@test alphasat(MVHSTableau, β, ∧(⊤, ⊤), Ł4) == true

@test alphasat(MVHSTableau, ⊤, ∧(⊥, ⊥), Ł4) == false
@test alphasat(MVHSTableau, ⊤, ∧(⊥, α), Ł4) == false
@test alphasat(MVHSTableau, ⊤, ∧(⊥, β), Ł4) == false
@test alphasat(MVHSTableau, ⊤, ∧(⊥, ⊤), Ł4) == false
@test alphasat(MVHSTableau, ⊤, ∧(α, ⊥), Ł4) == false
@test alphasat(MVHSTableau, ⊤, ∧(α, α), Ł4) == false
@test alphasat(MVHSTableau, ⊤, ∧(α, β), Ł4) == false
@test alphasat(MVHSTableau, ⊤, ∧(α, ⊤), Ł4) == false
@test alphasat(MVHSTableau, ⊤, ∧(β, ⊥), Ł4) == false
@test alphasat(MVHSTableau, ⊤, ∧(β, α), Ł4) == false
@test alphasat(MVHSTableau, ⊤, ∧(β, β), Ł4) == false
@test alphasat(MVHSTableau, ⊤, ∧(β, ⊤), Ł4) == false
@test alphasat(MVHSTableau, ⊤, ∧(⊤, ⊥), Ł4) == false
@test alphasat(MVHSTableau, ⊤, ∧(⊤, α), Ł4) == false
@test alphasat(MVHSTableau, ⊤, ∧(⊤, β), Ł4) == false
@test alphasat(MVHSTableau, ⊤, ∧(⊤, ⊤), Ł4) == true

@test alphasat(MVHSTableau, ⊥, ∧(parseformula("p"), ⊥), Ł4) == true
@test alphasat(MVHSTableau, ⊥, ∧(parseformula("p"), α), Ł4) == true
@test alphasat(MVHSTableau, ⊥, ∧(parseformula("p"), β), Ł4) == true
@test alphasat(MVHSTableau, ⊥, ∧(parseformula("p"), ⊤), Ł4) == true
@test alphasat(MVHSTableau, α, ∧(parseformula("p"), ⊥), Ł4) == false
@test alphasat(MVHSTableau, α, ∧(parseformula("p"), α), Ł4) == true
@test alphasat(MVHSTableau, α, ∧(parseformula("p"), β), Ł4) == true
@test alphasat(MVHSTableau, α, ∧(parseformula("p"), ⊤), Ł4) == true
@test alphasat(MVHSTableau, β, ∧(parseformula("p"), ⊥), Ł4) == false
@test alphasat(MVHSTableau, β, ∧(parseformula("p"), α), Ł4) == false
@test alphasat(MVHSTableau, β, ∧(parseformula("p"), β), Ł4) == true
@test alphasat(MVHSTableau, β, ∧(parseformula("p"), ⊤), Ł4) == true
@test alphasat(MVHSTableau, ⊤, ∧(parseformula("p"), ⊥), Ł4) == false
@test alphasat(MVHSTableau, ⊤, ∧(parseformula("p"), α), Ł4) == false
@test alphasat(MVHSTableau, ⊤, ∧(parseformula("p"), β), Ł4) == false
@test alphasat(MVHSTableau, ⊤, ∧(parseformula("p"), ⊤), Ł4) == true

@test alphasat(MVHSTableau, ⊥, ∧(⊥, parseformula("p")), Ł4) == true
@test alphasat(MVHSTableau, ⊥, ∧(α, parseformula("p")), Ł4) == true
@test alphasat(MVHSTableau, ⊥, ∧(β, parseformula("p")), Ł4) == true
@test alphasat(MVHSTableau, ⊥, ∧(⊤, parseformula("p")), Ł4) == true
@test alphasat(MVHSTableau, α, ∧(⊥, parseformula("p")), Ł4) == false
@test alphasat(MVHSTableau, α, ∧(α, parseformula("p")), Ł4) == true
@test alphasat(MVHSTableau, α, ∧(β, parseformula("p")), Ł4) == true
@test alphasat(MVHSTableau, α, ∧(⊤, parseformula("p")), Ł4) == true
@test alphasat(MVHSTableau, β, ∧(⊥, parseformula("p")), Ł4) == false
@test alphasat(MVHSTableau, β, ∧(α, parseformula("p")), Ł4) == false
@test alphasat(MVHSTableau, β, ∧(β, parseformula("p")), Ł4) == true
@test alphasat(MVHSTableau, β, ∧(⊤, parseformula("p")), Ł4) == true
@test alphasat(MVHSTableau, ⊤, ∧(⊥, parseformula("p")), Ł4) == false
@test alphasat(MVHSTableau, ⊤, ∧(α, parseformula("p")), Ł4) == false
@test alphasat(MVHSTableau, ⊤, ∧(β, parseformula("p")), Ł4) == false
@test alphasat(MVHSTableau, ⊤, ∧(⊤, parseformula("p")), Ł4) == true

@test alphasat(MVHSTableau, ⊥, ∧(parseformula("p"), parseformula("p")), Ł4)
@test alphasat(MVHSTableau, α, ∧(parseformula("p"), parseformula("p")), Ł4)
@test alphasat(MVHSTableau, β, ∧(parseformula("p"), parseformula("p")), Ł4)
@test alphasat(MVHSTableau, ⊤, ∧(parseformula("p"), parseformula("p")), Ł4)

@test alphasat(MVHSTableau, ⊥, ∧(parseformula("p"), parseformula("q")), Ł4)
@test alphasat(MVHSTableau, α, ∧(parseformula("p"), parseformula("q")), Ł4)
@test alphasat(MVHSTableau, β, ∧(parseformula("p"), parseformula("q")), Ł4)
@test alphasat(MVHSTableau, ⊤, ∧(parseformula("p"), parseformula("q")), Ł4)

@test alphasat(MVHSTableau, ⊥, ∧(parseformula("q"), parseformula("p")), Ł4)
@test alphasat(MVHSTableau, α, ∧(parseformula("q"), parseformula("p")), Ł4)
@test alphasat(MVHSTableau, β, ∧(parseformula("q"), parseformula("p")), Ł4)
@test alphasat(MVHSTableau, ⊤, ∧(parseformula("q"), parseformula("p")), Ł4)

################################################################################
## Implication #################################################################
################################################################################

@test alphasat(MVHSTableau, ⊥, →(⊥, ⊥), Ł4) == true
@test alphasat(MVHSTableau, ⊥, →(⊥, α), Ł4) == true
@test alphasat(MVHSTableau, ⊥, →(⊥, β), Ł4) == true
@test alphasat(MVHSTableau, ⊥, →(⊥, ⊤), Ł4) == true
@test alphasat(MVHSTableau, ⊥, →(α, ⊥), Ł4) == true
@test alphasat(MVHSTableau, ⊥, →(α, α), Ł4) == true
@test alphasat(MVHSTableau, ⊥, →(α, β), Ł4) == true
@test alphasat(MVHSTableau, ⊥, →(α, ⊤), Ł4) == true
@test alphasat(MVHSTableau, ⊥, →(β, ⊥), Ł4) == true
@test alphasat(MVHSTableau, ⊥, →(β, α), Ł4) == true
@test alphasat(MVHSTableau, ⊥, →(β, β), Ł4) == true
@test alphasat(MVHSTableau, ⊥, →(β, ⊤), Ł4) == true
@test alphasat(MVHSTableau, ⊥, →(⊤, ⊥), Ł4) == true
@test alphasat(MVHSTableau, ⊥, →(⊤, α), Ł4) == true
@test alphasat(MVHSTableau, ⊥, →(⊤, β), Ł4) == true
@test alphasat(MVHSTableau, ⊥, →(⊤, ⊤), Ł4) == true

@test alphasat(MVHSTableau, α, →(⊥, ⊥), Ł4) == true
@test alphasat(MVHSTableau, α, →(⊥, α), Ł4) == true
@test alphasat(MVHSTableau, α, →(⊥, β), Ł4) == true
@test alphasat(MVHSTableau, α, →(⊥, ⊤), Ł4) == true
@test alphasat(MVHSTableau, α, →(α, ⊥), Ł4) == true
@test alphasat(MVHSTableau, α, →(α, α), Ł4) == true
@test alphasat(MVHSTableau, α, →(α, β), Ł4) == true
@test alphasat(MVHSTableau, α, →(α, ⊤), Ł4) == true
@test alphasat(MVHSTableau, α, →(β, ⊥), Ł4) == true
@test alphasat(MVHSTableau, α, →(β, α), Ł4) == true
@test alphasat(MVHSTableau, α, →(β, β), Ł4) == true
@test alphasat(MVHSTableau, α, →(β, ⊤), Ł4) == true
@test alphasat(MVHSTableau, α, →(⊤, ⊥), Ł4) == false
@test alphasat(MVHSTableau, α, →(⊤, α), Ł4) == true
@test alphasat(MVHSTableau, α, →(⊤, β), Ł4) == true
@test alphasat(MVHSTableau, α, →(⊤, ⊤), Ł4) == true

@test alphasat(MVHSTableau, β, →(⊥, ⊥), Ł4) == true
@test alphasat(MVHSTableau, β, →(⊥, α), Ł4) == true
@test alphasat(MVHSTableau, β, →(⊥, β), Ł4) == true
@test alphasat(MVHSTableau, β, →(⊥, ⊤), Ł4) == true
@test alphasat(MVHSTableau, β, →(α, ⊥), Ł4) == true
@test alphasat(MVHSTableau, β, →(α, α), Ł4) == true
@test alphasat(MVHSTableau, β, →(α, β), Ł4) == true
@test alphasat(MVHSTableau, β, →(α, ⊤), Ł4) == true
@test alphasat(MVHSTableau, β, →(β, ⊥), Ł4) == false
@test alphasat(MVHSTableau, β, →(β, α), Ł4) == true
@test alphasat(MVHSTableau, β, →(β, β), Ł4) == true
@test alphasat(MVHSTableau, β, →(β, ⊤), Ł4) == true
@test alphasat(MVHSTableau, β, →(⊤, ⊥), Ł4) == false
@test alphasat(MVHSTableau, β, →(⊤, α), Ł4) == false
@test alphasat(MVHSTableau, β, →(⊤, β), Ł4) == true
@test alphasat(MVHSTableau, β, →(⊤, ⊤), Ł4) == true

@test alphasat(MVHSTableau, ⊤, →(⊥, ⊥), Ł4) == true
@test alphasat(MVHSTableau, ⊤, →(⊥, α), Ł4) == true
@test alphasat(MVHSTableau, ⊤, →(⊥, β), Ł4) == true
@test alphasat(MVHSTableau, ⊤, →(⊥, ⊤), Ł4) == true
@test alphasat(MVHSTableau, ⊤, →(α, ⊥), Ł4) == false
@test alphasat(MVHSTableau, ⊤, →(α, α), Ł4) == true
@test alphasat(MVHSTableau, ⊤, →(α, β), Ł4) == true
@test alphasat(MVHSTableau, ⊤, →(α, ⊤), Ł4) == true
@test alphasat(MVHSTableau, ⊤, →(β, ⊥), Ł4) == false
@test alphasat(MVHSTableau, ⊤, →(β, α), Ł4) == false
@test alphasat(MVHSTableau, ⊤, →(β, β), Ł4) == true
@test alphasat(MVHSTableau, ⊤, →(β, ⊤), Ł4) == true
@test alphasat(MVHSTableau, ⊤, →(⊤, ⊥), Ł4) == false
@test alphasat(MVHSTableau, ⊤, →(⊤, α), Ł4) == false
@test alphasat(MVHSTableau, ⊤, →(⊤, β), Ł4) == false
@test alphasat(MVHSTableau, ⊤, →(⊤, ⊤), Ł4) == true

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
)), Ł4) == false
