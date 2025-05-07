################################################################################
#### Ł4 ########################################################################
################################################################################

using SoleLogics.ManyValuedLogics: Ł4
using SoleLogics.ManyValuedLogics: α, β

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

@test alphasat(MVLTLFPTableau, ⊥, parseformula("p"), Ł4) == true
@test alphasat(MVLTLFPTableau, α, parseformula("p"), Ł4) == true
@test alphasat(MVLTLFPTableau, β, parseformula("p"), Ł4) == true
@test alphasat(MVLTLFPTableau, ⊤, parseformula("p"), Ł4) == true

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

@test alphasat(MVLTLFPTableau, ⊥, ∨(parseformula("p"), ⊥), Ł4) == true
@test alphasat(MVLTLFPTableau, ⊥, ∨(parseformula("p"), α), Ł4) == true
@test alphasat(MVLTLFPTableau, ⊥, ∨(parseformula("p"), β), Ł4) == true
@test alphasat(MVLTLFPTableau, ⊥, ∨(parseformula("p"), ⊤), Ł4) == true
@test alphasat(MVLTLFPTableau, α, ∨(parseformula("p"), ⊥), Ł4) == true
@test alphasat(MVLTLFPTableau, α, ∨(parseformula("p"), α), Ł4) == true
@test alphasat(MVLTLFPTableau, α, ∨(parseformula("p"), β), Ł4) == true
@test alphasat(MVLTLFPTableau, α, ∨(parseformula("p"), ⊤), Ł4) == true
@test alphasat(MVLTLFPTableau, β, ∨(parseformula("p"), ⊥), Ł4) == true
@test alphasat(MVLTLFPTableau, β, ∨(parseformula("p"), α), Ł4) == true
@test alphasat(MVLTLFPTableau, β, ∨(parseformula("p"), β), Ł4) == true
@test alphasat(MVLTLFPTableau, β, ∨(parseformula("p"), ⊤), Ł4) == true
@test alphasat(MVLTLFPTableau, ⊤, ∨(parseformula("p"), ⊥), Ł4) == true
@test alphasat(MVLTLFPTableau, ⊤, ∨(parseformula("p"), α), Ł4) == true
@test alphasat(MVLTLFPTableau, ⊤, ∨(parseformula("p"), β), Ł4) == true
@test alphasat(MVLTLFPTableau, ⊤, ∨(parseformula("p"), ⊤), Ł4) == true

@test alphasat(MVLTLFPTableau, ⊥, ∨(⊥, parseformula("p")), Ł4) == true
@test alphasat(MVLTLFPTableau, ⊥, ∨(α, parseformula("p")), Ł4) == true
@test alphasat(MVLTLFPTableau, ⊥, ∨(β, parseformula("p")), Ł4) == true
@test alphasat(MVLTLFPTableau, ⊥, ∨(⊤, parseformula("p")), Ł4) == true
@test alphasat(MVLTLFPTableau, α, ∨(⊥, parseformula("p")), Ł4) == true
@test alphasat(MVLTLFPTableau, α, ∨(α, parseformula("p")), Ł4) == true
@test alphasat(MVLTLFPTableau, α, ∨(β, parseformula("p")), Ł4) == true
@test alphasat(MVLTLFPTableau, α, ∨(⊤, parseformula("p")), Ł4) == true
@test alphasat(MVLTLFPTableau, β, ∨(⊥, parseformula("p")), Ł4) == true
@test alphasat(MVLTLFPTableau, β, ∨(α, parseformula("p")), Ł4) == true
@test alphasat(MVLTLFPTableau, β, ∨(β, parseformula("p")), Ł4) == true
@test alphasat(MVLTLFPTableau, β, ∨(⊤, parseformula("p")), Ł4) == true
@test alphasat(MVLTLFPTableau, ⊤, ∨(⊥, parseformula("p")), Ł4) == true
@test alphasat(MVLTLFPTableau, ⊤, ∨(α, parseformula("p")), Ł4) == true
@test alphasat(MVLTLFPTableau, ⊤, ∨(β, parseformula("p")), Ł4) == true
@test alphasat(MVLTLFPTableau, ⊤, ∨(⊤, parseformula("p")), Ł4) == true

@test alphasat(MVLTLFPTableau, ⊥, ∨(parseformula("p"), parseformula("p")), Ł4)
@test alphasat(MVLTLFPTableau, α, ∨(parseformula("p"), parseformula("p")), Ł4)
@test alphasat(MVLTLFPTableau, β, ∨(parseformula("p"), parseformula("p")), Ł4)
@test alphasat(MVLTLFPTableau, ⊤, ∨(parseformula("p"), parseformula("p")), Ł4)

@test alphasat(MVLTLFPTableau, ⊥, ∨(parseformula("p"), parseformula("q")), Ł4)
@test alphasat(MVLTLFPTableau, α, ∨(parseformula("p"), parseformula("q")), Ł4)
@test alphasat(MVLTLFPTableau, β, ∨(parseformula("p"), parseformula("q")), Ł4)
@test alphasat(MVLTLFPTableau, ⊤, ∨(parseformula("p"), parseformula("q")), Ł4)

@test alphasat(MVLTLFPTableau, ⊥, ∨(parseformula("q"), parseformula("q")), Ł4)
@test alphasat(MVLTLFPTableau, α, ∨(parseformula("q"), parseformula("q")), Ł4)
@test alphasat(MVLTLFPTableau, β, ∨(parseformula("q"), parseformula("q")), Ł4)
@test alphasat(MVLTLFPTableau, ⊤, ∨(parseformula("q"), parseformula("q")), Ł4)

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

@test alphasat(MVLTLFPTableau, ⊥, ∧(parseformula("p"), ⊥), Ł4) == true
@test alphasat(MVLTLFPTableau, ⊥, ∧(parseformula("p"), α), Ł4) == true
@test alphasat(MVLTLFPTableau, ⊥, ∧(parseformula("p"), β), Ł4) == true
@test alphasat(MVLTLFPTableau, ⊥, ∧(parseformula("p"), ⊤), Ł4) == true
@test alphasat(MVLTLFPTableau, α, ∧(parseformula("p"), ⊥), Ł4) == false
@test alphasat(MVLTLFPTableau, α, ∧(parseformula("p"), α), Ł4) == true
@test alphasat(MVLTLFPTableau, α, ∧(parseformula("p"), β), Ł4) == true
@test alphasat(MVLTLFPTableau, α, ∧(parseformula("p"), ⊤), Ł4) == true
@test alphasat(MVLTLFPTableau, β, ∧(parseformula("p"), ⊥), Ł4) == false
@test alphasat(MVLTLFPTableau, β, ∧(parseformula("p"), α), Ł4) == false
@test alphasat(MVLTLFPTableau, β, ∧(parseformula("p"), β), Ł4) == true
@test alphasat(MVLTLFPTableau, β, ∧(parseformula("p"), ⊤), Ł4) == true
@test alphasat(MVLTLFPTableau, ⊤, ∧(parseformula("p"), ⊥), Ł4) == false
@test alphasat(MVLTLFPTableau, ⊤, ∧(parseformula("p"), α), Ł4) == false
@test alphasat(MVLTLFPTableau, ⊤, ∧(parseformula("p"), β), Ł4) == false
@test alphasat(MVLTLFPTableau, ⊤, ∧(parseformula("p"), ⊤), Ł4) == true

@test alphasat(MVLTLFPTableau, ⊥, ∧(⊥, parseformula("p")), Ł4) == true
@test alphasat(MVLTLFPTableau, ⊥, ∧(α, parseformula("p")), Ł4) == true
@test alphasat(MVLTLFPTableau, ⊥, ∧(β, parseformula("p")), Ł4) == true
@test alphasat(MVLTLFPTableau, ⊥, ∧(⊤, parseformula("p")), Ł4) == true
@test alphasat(MVLTLFPTableau, α, ∧(⊥, parseformula("p")), Ł4) == false
@test alphasat(MVLTLFPTableau, α, ∧(α, parseformula("p")), Ł4) == true
@test alphasat(MVLTLFPTableau, α, ∧(β, parseformula("p")), Ł4) == true
@test alphasat(MVLTLFPTableau, α, ∧(⊤, parseformula("p")), Ł4) == true
@test alphasat(MVLTLFPTableau, β, ∧(⊥, parseformula("p")), Ł4) == false
@test alphasat(MVLTLFPTableau, β, ∧(α, parseformula("p")), Ł4) == false
@test alphasat(MVLTLFPTableau, β, ∧(β, parseformula("p")), Ł4) == true
@test alphasat(MVLTLFPTableau, β, ∧(⊤, parseformula("p")), Ł4) == true
@test alphasat(MVLTLFPTableau, ⊤, ∧(⊥, parseformula("p")), Ł4) == false
@test alphasat(MVLTLFPTableau, ⊤, ∧(α, parseformula("p")), Ł4) == false
@test alphasat(MVLTLFPTableau, ⊤, ∧(β, parseformula("p")), Ł4) == false
@test alphasat(MVLTLFPTableau, ⊤, ∧(⊤, parseformula("p")), Ł4) == true

@test alphasat(MVLTLFPTableau, ⊥, ∧(parseformula("p"), parseformula("p")), Ł4)
@test alphasat(MVLTLFPTableau, α, ∧(parseformula("p"), parseformula("p")), Ł4)
@test alphasat(MVLTLFPTableau, β, ∧(parseformula("p"), parseformula("p")), Ł4)
@test alphasat(MVLTLFPTableau, ⊤, ∧(parseformula("p"), parseformula("p")), Ł4)

@test alphasat(MVLTLFPTableau, ⊥, ∧(parseformula("p"), parseformula("q")), Ł4)
@test alphasat(MVLTLFPTableau, α, ∧(parseformula("p"), parseformula("q")), Ł4)
@test alphasat(MVLTLFPTableau, β, ∧(parseformula("p"), parseformula("q")), Ł4)
@test alphasat(MVLTLFPTableau, ⊤, ∧(parseformula("p"), parseformula("q")), Ł4)

@test alphasat(MVLTLFPTableau, ⊥, ∧(parseformula("q"), parseformula("p")), Ł4)
@test alphasat(MVLTLFPTableau, α, ∧(parseformula("q"), parseformula("p")), Ł4)
@test alphasat(MVLTLFPTableau, β, ∧(parseformula("q"), parseformula("p")), Ł4)
@test alphasat(MVLTLFPTableau, ⊤, ∧(parseformula("q"), parseformula("p")), Ł4)

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
)), Ł4) == false
