############################################################################################
#### H4 ####################################################################################
############################################################################################

using SoleLogics.ManyValuedLogics: H4
using SoleLogics.ManyValuedLogics: α, β

############################################################################################
## Base cases ##############################################################################
############################################################################################

@test mvhsalphasat(⊥, ⊥, FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(⊥, α, FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(⊥, β, FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(⊥, ⊤, FiniteHeytingAlgebra(H4)) == true

@test mvhsalphasat(α, ⊥, FiniteHeytingAlgebra(H4)) == false
@test mvhsalphasat(α, α, FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(α, β, FiniteHeytingAlgebra(H4)) == false
@test mvhsalphasat(α, ⊤, FiniteHeytingAlgebra(H4)) == true

@test mvhsalphasat(β, ⊥, FiniteHeytingAlgebra(H4)) == false
@test mvhsalphasat(β, α, FiniteHeytingAlgebra(H4)) == false
@test mvhsalphasat(β, β, FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(β, ⊤, FiniteHeytingAlgebra(H4)) == true

@test mvhsalphasat(⊤, ⊥, FiniteHeytingAlgebra(H4)) == false
@test mvhsalphasat(⊤, α, FiniteHeytingAlgebra(H4)) == false
@test mvhsalphasat(⊤, β, FiniteHeytingAlgebra(H4)) == false
@test mvhsalphasat(⊤, ⊤, FiniteHeytingAlgebra(H4)) == true

@test mvhsalphasat(⊥, parseformula("p"), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(α, parseformula("p"), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(β, parseformula("p"), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(⊤, parseformula("p"), FiniteHeytingAlgebra(H4)) == true

############################################################################################
## (Strong) disjuction #####################################################################
############################################################################################

@test mvhsalphasat(⊥, ∨(⊥, ⊥), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(⊥, ∨(⊥, α), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(⊥, ∨(⊥, β), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(⊥, ∨(⊥, ⊤), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(⊥, ∨(α, ⊥), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(⊥, ∨(α, α), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(⊥, ∨(α, β), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(⊥, ∨(α, ⊤), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(⊥, ∨(β, ⊥), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(⊥, ∨(β, α), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(⊥, ∨(β, β), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(⊥, ∨(β, ⊤), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(⊥, ∨(⊤, ⊥), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(⊥, ∨(⊤, α), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(⊥, ∨(⊤, β), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(⊥, ∨(⊤, ⊤), FiniteHeytingAlgebra(H4)) == true

@test mvhsalphasat(α, ∨(⊥, ⊥), FiniteHeytingAlgebra(H4)) == false
@test mvhsalphasat(α, ∨(⊥, α), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(α, ∨(⊥, β), FiniteHeytingAlgebra(H4)) == false
@test mvhsalphasat(α, ∨(⊥, ⊤), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(α, ∨(α, ⊥), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(α, ∨(α, α), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(α, ∨(α, β), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(α, ∨(α, ⊤), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(α, ∨(β, ⊥), FiniteHeytingAlgebra(H4)) == false
@test mvhsalphasat(α, ∨(β, α), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(α, ∨(β, β), FiniteHeytingAlgebra(H4)) == false
@test mvhsalphasat(α, ∨(β, ⊤), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(α, ∨(⊤, ⊥), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(α, ∨(⊤, α), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(α, ∨(⊤, β), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(α, ∨(⊤, ⊤), FiniteHeytingAlgebra(H4)) == true

@test mvhsalphasat(β, ∨(⊥, ⊥), FiniteHeytingAlgebra(H4)) == false
@test mvhsalphasat(β, ∨(⊥, α), FiniteHeytingAlgebra(H4)) == false
@test mvhsalphasat(β, ∨(⊥, β), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(β, ∨(⊥, ⊤), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(β, ∨(α, ⊥), FiniteHeytingAlgebra(H4)) == false
@test mvhsalphasat(β, ∨(α, α), FiniteHeytingAlgebra(H4)) == false
@test mvhsalphasat(β, ∨(α, β), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(β, ∨(α, ⊤), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(β, ∨(β, ⊥), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(β, ∨(β, α), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(β, ∨(β, β), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(β, ∨(β, ⊤), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(β, ∨(⊤, ⊥), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(β, ∨(⊤, α), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(β, ∨(⊤, β), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(β, ∨(⊤, ⊤), FiniteHeytingAlgebra(H4)) == true

@test mvhsalphasat(⊤, ∨(⊥, ⊥), FiniteHeytingAlgebra(H4)) == false
@test mvhsalphasat(⊤, ∨(⊥, α), FiniteHeytingAlgebra(H4)) == false
@test mvhsalphasat(⊤, ∨(⊥, β), FiniteHeytingAlgebra(H4)) == false
@test mvhsalphasat(⊤, ∨(⊥, ⊤), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(⊤, ∨(α, ⊥), FiniteHeytingAlgebra(H4)) == false
@test mvhsalphasat(⊤, ∨(α, α), FiniteHeytingAlgebra(H4)) == false
@test mvhsalphasat(⊤, ∨(α, β), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(⊤, ∨(α, ⊤), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(⊤, ∨(β, ⊥), FiniteHeytingAlgebra(H4)) == false
@test mvhsalphasat(⊤, ∨(β, α), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(⊤, ∨(β, β), FiniteHeytingAlgebra(H4)) == false
@test mvhsalphasat(⊤, ∨(β, ⊤), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(⊤, ∨(⊤, ⊥), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(⊤, ∨(⊤, α), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(⊤, ∨(⊤, β), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(⊤, ∨(⊤, ⊤), FiniteHeytingAlgebra(H4)) == true

@test mvhsalphasat(⊥, ∨(parseformula("p"), ⊥), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(⊥, ∨(parseformula("p"), α), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(⊥, ∨(parseformula("p"), β), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(⊥, ∨(parseformula("p"), ⊤), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(α, ∨(parseformula("p"), ⊥), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(α, ∨(parseformula("p"), α), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(α, ∨(parseformula("p"), β), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(α, ∨(parseformula("p"), ⊤), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(β, ∨(parseformula("p"), ⊥), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(β, ∨(parseformula("p"), α), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(β, ∨(parseformula("p"), β), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(β, ∨(parseformula("p"), ⊤), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(⊤, ∨(parseformula("p"), ⊥), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(⊤, ∨(parseformula("p"), α), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(⊤, ∨(parseformula("p"), β), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(⊤, ∨(parseformula("p"), ⊤), FiniteHeytingAlgebra(H4)) == true

@test mvhsalphasat(⊥, ∨(⊥, parseformula("p")), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(⊥, ∨(α, parseformula("p")), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(⊥, ∨(β, parseformula("p")), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(⊥, ∨(⊤, parseformula("p")), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(α, ∨(⊥, parseformula("p")), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(α, ∨(α, parseformula("p")), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(α, ∨(β, parseformula("p")), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(α, ∨(⊤, parseformula("p")), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(β, ∨(⊥, parseformula("p")), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(β, ∨(α, parseformula("p")), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(β, ∨(β, parseformula("p")), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(β, ∨(⊤, parseformula("p")), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(⊤, ∨(⊥, parseformula("p")), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(⊤, ∨(α, parseformula("p")), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(⊤, ∨(β, parseformula("p")), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(⊤, ∨(⊤, parseformula("p")), FiniteHeytingAlgebra(H4)) == true

@test mvhsalphasat(⊥, ∨(parseformula("p"), parseformula("p")), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(α, ∨(parseformula("p"), parseformula("p")), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(β, ∨(parseformula("p"), parseformula("p")), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(⊤, ∨(parseformula("p"), parseformula("p")), FiniteHeytingAlgebra(H4)) == true

@test mvhsalphasat(⊥, ∨(parseformula("p"), parseformula("q")), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(α, ∨(parseformula("p"), parseformula("q")), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(β, ∨(parseformula("p"), parseformula("q")), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(⊤, ∨(parseformula("p"), parseformula("q")), FiniteHeytingAlgebra(H4)) == true

@test mvhsalphasat(⊥, ∨(parseformula("q"), parseformula("q")), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(α, ∨(parseformula("q"), parseformula("q")), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(β, ∨(parseformula("q"), parseformula("q")), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(⊤, ∨(parseformula("q"), parseformula("q")), FiniteHeytingAlgebra(H4)) == true

############################################################################################
## (Strong) conjunction ####################################################################
############################################################################################

@test mvhsalphasat(⊥, ∧(⊥, ⊥), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(⊥, ∧(⊥, α), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(⊥, ∧(⊥, β), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(⊥, ∧(⊥, ⊤), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(⊥, ∧(α, ⊥), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(⊥, ∧(α, α), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(⊥, ∧(α, β), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(⊥, ∧(α, ⊤), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(⊥, ∧(β, ⊥), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(⊥, ∧(β, α), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(⊥, ∧(β, β), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(⊥, ∧(β, ⊤), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(⊥, ∧(⊤, ⊥), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(⊥, ∧(⊤, α), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(⊥, ∧(⊤, β), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(⊥, ∧(⊤, ⊤), FiniteHeytingAlgebra(H4)) == true

@test mvhsalphasat(α, ∧(⊥, ⊥), FiniteHeytingAlgebra(H4)) == false
@test mvhsalphasat(α, ∧(⊥, α), FiniteHeytingAlgebra(H4)) == false
@test mvhsalphasat(α, ∧(⊥, β), FiniteHeytingAlgebra(H4)) == false
@test mvhsalphasat(α, ∧(⊥, ⊤), FiniteHeytingAlgebra(H4)) == false
@test mvhsalphasat(α, ∧(α, ⊥), FiniteHeytingAlgebra(H4)) == false
@test mvhsalphasat(α, ∧(α, α), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(α, ∧(α, β), FiniteHeytingAlgebra(H4)) == false
@test mvhsalphasat(α, ∧(α, ⊤), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(α, ∧(β, ⊥), FiniteHeytingAlgebra(H4)) == false
@test mvhsalphasat(α, ∧(β, α), FiniteHeytingAlgebra(H4)) == false
@test mvhsalphasat(α, ∧(β, β), FiniteHeytingAlgebra(H4)) == false
@test mvhsalphasat(α, ∧(β, ⊤), FiniteHeytingAlgebra(H4)) == false
@test mvhsalphasat(α, ∧(⊤, ⊥), FiniteHeytingAlgebra(H4)) == false
@test mvhsalphasat(α, ∧(⊤, α), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(α, ∧(⊤, β), FiniteHeytingAlgebra(H4)) == false
@test mvhsalphasat(α, ∧(⊤, ⊤), FiniteHeytingAlgebra(H4)) == true

@test mvhsalphasat(β, ∧(⊥, ⊥), FiniteHeytingAlgebra(H4)) == false
@test mvhsalphasat(β, ∧(⊥, α), FiniteHeytingAlgebra(H4)) == false
@test mvhsalphasat(β, ∧(⊥, β), FiniteHeytingAlgebra(H4)) == false
@test mvhsalphasat(β, ∧(⊥, ⊤), FiniteHeytingAlgebra(H4)) == false
@test mvhsalphasat(β, ∧(α, ⊥), FiniteHeytingAlgebra(H4)) == false
@test mvhsalphasat(β, ∧(α, α), FiniteHeytingAlgebra(H4)) == false
@test mvhsalphasat(β, ∧(α, β), FiniteHeytingAlgebra(H4)) == false
@test mvhsalphasat(β, ∧(α, ⊤), FiniteHeytingAlgebra(H4)) == false
@test mvhsalphasat(β, ∧(β, ⊥), FiniteHeytingAlgebra(H4)) == false
@test mvhsalphasat(β, ∧(β, α), FiniteHeytingAlgebra(H4)) == false
@test mvhsalphasat(β, ∧(β, β), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(β, ∧(β, ⊤), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(β, ∧(⊤, ⊥), FiniteHeytingAlgebra(H4)) == false
@test mvhsalphasat(β, ∧(⊤, α), FiniteHeytingAlgebra(H4)) == false
@test mvhsalphasat(β, ∧(⊤, β), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(β, ∧(⊤, ⊤), FiniteHeytingAlgebra(H4)) == true

@test mvhsalphasat(⊤, ∧(⊥, ⊥), FiniteHeytingAlgebra(H4)) == false
@test mvhsalphasat(⊤, ∧(⊥, α), FiniteHeytingAlgebra(H4)) == false
@test mvhsalphasat(⊤, ∧(⊥, β), FiniteHeytingAlgebra(H4)) == false
@test mvhsalphasat(⊤, ∧(⊥, ⊤), FiniteHeytingAlgebra(H4)) == false
@test mvhsalphasat(⊤, ∧(α, ⊥), FiniteHeytingAlgebra(H4)) == false
@test mvhsalphasat(⊤, ∧(α, α), FiniteHeytingAlgebra(H4)) == false
@test mvhsalphasat(⊤, ∧(α, β), FiniteHeytingAlgebra(H4)) == false
@test mvhsalphasat(⊤, ∧(α, ⊤), FiniteHeytingAlgebra(H4)) == false
@test mvhsalphasat(⊤, ∧(β, ⊥), FiniteHeytingAlgebra(H4)) == false
@test mvhsalphasat(⊤, ∧(β, α), FiniteHeytingAlgebra(H4)) == false
@test mvhsalphasat(⊤, ∧(β, β), FiniteHeytingAlgebra(H4)) == false
@test mvhsalphasat(⊤, ∧(β, ⊤), FiniteHeytingAlgebra(H4)) == false
@test mvhsalphasat(⊤, ∧(⊤, ⊥), FiniteHeytingAlgebra(H4)) == false
@test mvhsalphasat(⊤, ∧(⊤, α), FiniteHeytingAlgebra(H4)) == false
@test mvhsalphasat(⊤, ∧(⊤, β), FiniteHeytingAlgebra(H4)) == false
@test mvhsalphasat(⊤, ∧(⊤, ⊤), FiniteHeytingAlgebra(H4)) == true

@test mvhsalphasat(⊥, ∧(parseformula("p"), ⊥), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(⊥, ∧(parseformula("p"), α), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(⊥, ∧(parseformula("p"), β), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(⊥, ∧(parseformula("p"), ⊤), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(α, ∧(parseformula("p"), ⊥), FiniteHeytingAlgebra(H4)) == false
@test mvhsalphasat(α, ∧(parseformula("p"), α), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(α, ∧(parseformula("p"), β), FiniteHeytingAlgebra(H4)) == false
@test mvhsalphasat(α, ∧(parseformula("p"), ⊤), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(β, ∧(parseformula("p"), ⊥), FiniteHeytingAlgebra(H4)) == false
@test mvhsalphasat(β, ∧(parseformula("p"), α), FiniteHeytingAlgebra(H4)) == false
@test mvhsalphasat(β, ∧(parseformula("p"), β), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(β, ∧(parseformula("p"), ⊤), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(⊤, ∧(parseformula("p"), ⊥), FiniteHeytingAlgebra(H4)) == false
@test mvhsalphasat(⊤, ∧(parseformula("p"), α), FiniteHeytingAlgebra(H4)) == false
@test mvhsalphasat(⊤, ∧(parseformula("p"), β), FiniteHeytingAlgebra(H4)) == false
@test mvhsalphasat(⊤, ∧(parseformula("p"), ⊤), FiniteHeytingAlgebra(H4)) == true

@test mvhsalphasat(⊥, ∧(⊥, parseformula("p")), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(⊥, ∧(α, parseformula("p")), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(⊥, ∧(β, parseformula("p")), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(⊥, ∧(⊤, parseformula("p")), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(α, ∧(⊥, parseformula("p")), FiniteHeytingAlgebra(H4)) == false
@test mvhsalphasat(α, ∧(α, parseformula("p")), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(α, ∧(β, parseformula("p")), FiniteHeytingAlgebra(H4)) == false
@test mvhsalphasat(α, ∧(⊤, parseformula("p")), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(β, ∧(⊥, parseformula("p")), FiniteHeytingAlgebra(H4)) == false
@test mvhsalphasat(β, ∧(α, parseformula("p")), FiniteHeytingAlgebra(H4)) == false
@test mvhsalphasat(β, ∧(β, parseformula("p")), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(β, ∧(⊤, parseformula("p")), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(⊤, ∧(⊥, parseformula("p")), FiniteHeytingAlgebra(H4)) == false
@test mvhsalphasat(⊤, ∧(α, parseformula("p")), FiniteHeytingAlgebra(H4)) == false
@test mvhsalphasat(⊤, ∧(β, parseformula("p")), FiniteHeytingAlgebra(H4)) == false
@test mvhsalphasat(⊤, ∧(⊤, parseformula("p")), FiniteHeytingAlgebra(H4)) == true

@test mvhsalphasat(⊥, ∧(parseformula("p"), parseformula("p")), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(α, ∧(parseformula("p"), parseformula("p")), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(β, ∧(parseformula("p"), parseformula("p")), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(⊤, ∧(parseformula("p"), parseformula("p")), FiniteHeytingAlgebra(H4)) == true

@test mvhsalphasat(⊥, ∧(parseformula("p"), parseformula("q")), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(α, ∧(parseformula("p"), parseformula("q")), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(β, ∧(parseformula("p"), parseformula("q")), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(⊤, ∧(parseformula("p"), parseformula("q")), FiniteHeytingAlgebra(H4)) == true

@test mvhsalphasat(⊥, ∧(parseformula("q"), parseformula("p")), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(α, ∧(parseformula("q"), parseformula("p")), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(β, ∧(parseformula("q"), parseformula("p")), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(⊤, ∧(parseformula("q"), parseformula("p")), FiniteHeytingAlgebra(H4)) == true

############################################################################################
## Implication #############################################################################
############################################################################################

@test mvhsalphasat(⊥, →(⊥, ⊥), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(⊥, →(⊥, α), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(⊥, →(⊥, β), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(⊥, →(⊥, ⊤), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(⊥, →(α, ⊥), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(⊥, →(α, α), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(⊥, →(α, β), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(⊥, →(α, ⊤), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(⊥, →(β, ⊥), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(⊥, →(β, α), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(⊥, →(β, β), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(⊥, →(β, ⊤), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(⊥, →(⊤, ⊥), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(⊥, →(⊤, α), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(⊥, →(⊤, β), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(⊥, →(⊤, ⊤), FiniteHeytingAlgebra(H4)) == true

@test mvhsalphasat(α, →(⊥, ⊥), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(α, →(⊥, α), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(α, →(⊥, β), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(α, →(⊥, ⊤), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(α, →(α, ⊥), FiniteHeytingAlgebra(H4)) == false
@test mvhsalphasat(α, →(α, α), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(α, →(α, β), FiniteHeytingAlgebra(H4)) == false
@test mvhsalphasat(α, →(α, ⊤), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(α, →(β, ⊥), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(α, →(β, α), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(α, →(β, β), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(α, →(β, ⊤), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(α, →(⊤, ⊥), FiniteHeytingAlgebra(H4)) == false
@test mvhsalphasat(α, →(⊤, α), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(α, →(⊤, β), FiniteHeytingAlgebra(H4)) == false
@test mvhsalphasat(α, →(⊤, ⊤), FiniteHeytingAlgebra(H4)) == true

@test mvhsalphasat(β, →(⊥, ⊥), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(β, →(⊥, α), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(β, →(⊥, β), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(β, →(⊥, ⊤), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(β, →(α, ⊥), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(β, →(α, α), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(β, →(α, β), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(β, →(α, ⊤), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(β, →(β, ⊥), FiniteHeytingAlgebra(H4)) == false
@test mvhsalphasat(β, →(β, α), FiniteHeytingAlgebra(H4)) == false
@test mvhsalphasat(β, →(β, β), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(β, →(β, ⊤), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(β, →(⊤, ⊥), FiniteHeytingAlgebra(H4)) == false
@test mvhsalphasat(β, →(⊤, α), FiniteHeytingAlgebra(H4)) == false
@test mvhsalphasat(β, →(⊤, β), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(β, →(⊤, ⊤), FiniteHeytingAlgebra(H4)) == true

@test mvhsalphasat(⊤, →(⊥, ⊥), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(⊤, →(⊥, α), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(⊤, →(⊥, β), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(⊤, →(⊥, ⊤), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(⊤, →(α, ⊥), FiniteHeytingAlgebra(H4)) == false
@test mvhsalphasat(⊤, →(α, α), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(⊤, →(α, β), FiniteHeytingAlgebra(H4)) == false
@test mvhsalphasat(⊤, →(α, ⊤), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(⊤, →(β, ⊥), FiniteHeytingAlgebra(H4)) == false
@test mvhsalphasat(⊤, →(β, α), FiniteHeytingAlgebra(H4)) == false
@test mvhsalphasat(⊤, →(β, β), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(⊤, →(β, ⊤), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(⊤, →(⊤, ⊥), FiniteHeytingAlgebra(H4)) == false
@test mvhsalphasat(⊤, →(⊤, α), FiniteHeytingAlgebra(H4)) == false
@test mvhsalphasat(⊤, →(⊤, β), FiniteHeytingAlgebra(H4)) == false
@test mvhsalphasat(⊤, →(⊤, ⊤), FiniteHeytingAlgebra(H4)) == true

@test mvhsalphasat(⊥, →(parseformula("p"), ⊥), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(⊥, →(parseformula("p"), α), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(⊥, →(parseformula("p"), β), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(⊥, →(parseformula("p"), ⊤), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(α, →(parseformula("p"), ⊥), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(α, →(parseformula("p"), α), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(α, →(parseformula("p"), β), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(α, →(parseformula("p"), ⊤), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(β, →(parseformula("p"), ⊥), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(β, →(parseformula("p"), α), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(β, →(parseformula("p"), β), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(β, →(parseformula("p"), ⊤), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(⊤, →(parseformula("p"), ⊥), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(⊤, →(parseformula("p"), α), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(⊤, →(parseformula("p"), β), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(⊤, →(parseformula("p"), ⊤), FiniteHeytingAlgebra(H4)) == true

@test mvhsalphasat(⊥, →(⊥, parseformula("p")), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(⊥, →(α, parseformula("p")), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(⊥, →(β, parseformula("p")), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(⊥, →(⊤, parseformula("p")), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(α, →(⊥, parseformula("p")), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(α, →(α, parseformula("p")), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(α, →(β, parseformula("p")), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(α, →(⊤, parseformula("p")), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(β, →(⊥, parseformula("p")), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(β, →(α, parseformula("p")), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(β, →(β, parseformula("p")), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(β, →(⊤, parseformula("p")), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(⊤, →(⊥, parseformula("p")), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(⊤, →(α, parseformula("p")), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(⊤, →(β, parseformula("p")), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(⊤, →(⊤, parseformula("p")), FiniteHeytingAlgebra(H4)) == true

@test mvhsalphasat(⊥, →(parseformula("p"), parseformula("p")), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(α, →(parseformula("p"), parseformula("p")), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(β, →(parseformula("p"), parseformula("p")), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(⊤, →(parseformula("p"), parseformula("p")), FiniteHeytingAlgebra(H4)) == true

@test mvhsalphasat(⊥, →(parseformula("p"), parseformula("q")), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(α, →(parseformula("p"), parseformula("q")), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(β, →(parseformula("p"), parseformula("q")), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(⊤, →(parseformula("p"), parseformula("q")), FiniteHeytingAlgebra(H4)) == true

@test mvhsalphasat(⊥, →(parseformula("q"), parseformula("p")), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(α, →(parseformula("q"), parseformula("p")), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(β, →(parseformula("q"), parseformula("p")), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(⊤, →(parseformula("q"), parseformula("p")), FiniteHeytingAlgebra(H4)) == true
