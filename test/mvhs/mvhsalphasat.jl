max_timeout = 1 # seconds

############################################################################################
#### H4 ####################################################################################
############################################################################################

using SoleLogics.ManyValuedLogics: H4
using SoleLogics.ManyValuedLogics: α, β

############################################################################################
# Heyting Algebra ##########################################################################
############################################################################################
## Base cases ##############################################################################
############################################################################################

@test mvhsalphasat(⊥, ⊥, FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(⊥, α, FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(⊥, β, FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(⊥, ⊤, FiniteHeytingAlgebra(H4), timeout=max_timeout) == true

@test mvhsalphasat(α, ⊥, FiniteHeytingAlgebra(H4), timeout=max_timeout) == false
@test mvhsalphasat(α, α, FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(α, β, FiniteHeytingAlgebra(H4), timeout=max_timeout) == false
@test mvhsalphasat(α, ⊤, FiniteHeytingAlgebra(H4), timeout=max_timeout) == true

@test mvhsalphasat(β, ⊥, FiniteHeytingAlgebra(H4), timeout=max_timeout) == false
@test mvhsalphasat(β, α, FiniteHeytingAlgebra(H4), timeout=max_timeout) == false
@test mvhsalphasat(β, β, FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(β, ⊤, FiniteHeytingAlgebra(H4), timeout=max_timeout) == true

@test mvhsalphasat(⊤, ⊥, FiniteHeytingAlgebra(H4), timeout=max_timeout) == false
@test mvhsalphasat(⊤, α, FiniteHeytingAlgebra(H4), timeout=max_timeout) == false
@test mvhsalphasat(⊤, β, FiniteHeytingAlgebra(H4), timeout=max_timeout) == false
@test mvhsalphasat(⊤, ⊤, FiniteHeytingAlgebra(H4), timeout=max_timeout) == true

@test mvhsalphasat(⊥, parseformula("p"), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(α, parseformula("p"), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(β, parseformula("p"), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(⊤, parseformula("p"), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true

############################################################################################
## (Strong) disjuction #####################################################################
############################################################################################

@test mvhsalphasat(⊥, ∨(⊥, ⊥), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(⊥, ∨(⊥, α), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(⊥, ∨(⊥, β), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(⊥, ∨(⊥, ⊤), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(⊥, ∨(α, ⊥), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(⊥, ∨(α, α), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(⊥, ∨(α, β), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(⊥, ∨(α, ⊤), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(⊥, ∨(β, ⊥), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(⊥, ∨(β, α), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(⊥, ∨(β, β), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(⊥, ∨(β, ⊤), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(⊥, ∨(⊤, ⊥), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(⊥, ∨(⊤, α), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(⊥, ∨(⊤, β), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(⊥, ∨(⊤, ⊤), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true

@test mvhsalphasat(α, ∨(⊥, ⊥), FiniteHeytingAlgebra(H4), timeout=max_timeout) == false
@test mvhsalphasat(α, ∨(⊥, α), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(α, ∨(⊥, β), FiniteHeytingAlgebra(H4), timeout=max_timeout) == false
@test mvhsalphasat(α, ∨(⊥, ⊤), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(α, ∨(α, ⊥), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(α, ∨(α, α), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(α, ∨(α, β), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(α, ∨(α, ⊤), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(α, ∨(β, ⊥), FiniteHeytingAlgebra(H4), timeout=max_timeout) == false
@test mvhsalphasat(α, ∨(β, α), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(α, ∨(β, β), FiniteHeytingAlgebra(H4), timeout=max_timeout) == false
@test mvhsalphasat(α, ∨(β, ⊤), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(α, ∨(⊤, ⊥), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(α, ∨(⊤, α), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(α, ∨(⊤, β), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(α, ∨(⊤, ⊤), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true

@test mvhsalphasat(β, ∨(⊥, ⊥), FiniteHeytingAlgebra(H4), timeout=max_timeout) == false
@test mvhsalphasat(β, ∨(⊥, α), FiniteHeytingAlgebra(H4), timeout=max_timeout) == false
@test mvhsalphasat(β, ∨(⊥, β), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(β, ∨(⊥, ⊤), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(β, ∨(α, ⊥), FiniteHeytingAlgebra(H4), timeout=max_timeout) == false
@test mvhsalphasat(β, ∨(α, α), FiniteHeytingAlgebra(H4), timeout=max_timeout) == false
@test mvhsalphasat(β, ∨(α, β), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(β, ∨(α, ⊤), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(β, ∨(β, ⊥), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(β, ∨(β, α), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(β, ∨(β, β), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(β, ∨(β, ⊤), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(β, ∨(⊤, ⊥), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(β, ∨(⊤, α), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(β, ∨(⊤, β), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(β, ∨(⊤, ⊤), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true

@test mvhsalphasat(⊤, ∨(⊥, ⊥), FiniteHeytingAlgebra(H4), timeout=max_timeout) == false
@test mvhsalphasat(⊤, ∨(⊥, α), FiniteHeytingAlgebra(H4), timeout=max_timeout) == false
@test mvhsalphasat(⊤, ∨(⊥, β), FiniteHeytingAlgebra(H4), timeout=max_timeout) == false
@test mvhsalphasat(⊤, ∨(⊥, ⊤), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(⊤, ∨(α, ⊥), FiniteHeytingAlgebra(H4), timeout=max_timeout) == false
@test mvhsalphasat(⊤, ∨(α, α), FiniteHeytingAlgebra(H4), timeout=max_timeout) == false
@test mvhsalphasat(⊤, ∨(α, β), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(⊤, ∨(α, ⊤), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(⊤, ∨(β, ⊥), FiniteHeytingAlgebra(H4), timeout=max_timeout) == false
@test mvhsalphasat(⊤, ∨(β, α), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(⊤, ∨(β, β), FiniteHeytingAlgebra(H4), timeout=max_timeout) == false
@test mvhsalphasat(⊤, ∨(β, ⊤), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(⊤, ∨(⊤, ⊥), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(⊤, ∨(⊤, α), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(⊤, ∨(⊤, β), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(⊤, ∨(⊤, ⊤), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true

@test mvhsalphasat(⊥, ∨(parseformula("p"), ⊥), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(⊥, ∨(parseformula("p"), α), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(⊥, ∨(parseformula("p"), β), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(⊥, ∨(parseformula("p"), ⊤), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(α, ∨(parseformula("p"), ⊥), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(α, ∨(parseformula("p"), α), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(α, ∨(parseformula("p"), β), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(α, ∨(parseformula("p"), ⊤), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(β, ∨(parseformula("p"), ⊥), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(β, ∨(parseformula("p"), α), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(β, ∨(parseformula("p"), β), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(β, ∨(parseformula("p"), ⊤), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(⊤, ∨(parseformula("p"), ⊥), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(⊤, ∨(parseformula("p"), α), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(⊤, ∨(parseformula("p"), β), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(⊤, ∨(parseformula("p"), ⊤), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true

@test mvhsalphasat(⊥, ∨(⊥, parseformula("p")), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(⊥, ∨(α, parseformula("p")), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(⊥, ∨(β, parseformula("p")), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(⊥, ∨(⊤, parseformula("p")), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(α, ∨(⊥, parseformula("p")), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(α, ∨(α, parseformula("p")), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(α, ∨(β, parseformula("p")), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(α, ∨(⊤, parseformula("p")), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(β, ∨(⊥, parseformula("p")), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(β, ∨(α, parseformula("p")), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(β, ∨(β, parseformula("p")), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(β, ∨(⊤, parseformula("p")), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(⊤, ∨(⊥, parseformula("p")), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(⊤, ∨(α, parseformula("p")), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(⊤, ∨(β, parseformula("p")), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(⊤, ∨(⊤, parseformula("p")), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true

@test mvhsalphasat(⊥, ∨(parseformula("p"), parseformula("p")), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(α, ∨(parseformula("p"), parseformula("p")), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(β, ∨(parseformula("p"), parseformula("p")), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(⊤, ∨(parseformula("p"), parseformula("p")), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true

@test mvhsalphasat(⊥, ∨(parseformula("p"), parseformula("q")), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(α, ∨(parseformula("p"), parseformula("q")), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(β, ∨(parseformula("p"), parseformula("q")), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(⊤, ∨(parseformula("p"), parseformula("q")), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true

@test mvhsalphasat(⊥, ∨(parseformula("q"), parseformula("q")), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(α, ∨(parseformula("q"), parseformula("q")), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(β, ∨(parseformula("q"), parseformula("q")), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(⊤, ∨(parseformula("q"), parseformula("q")), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true

############################################################################################
## (Strong) conjunction ####################################################################
############################################################################################

@test mvhsalphasat(⊥, ∧(⊥, ⊥), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(⊥, ∧(⊥, α), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(⊥, ∧(⊥, β), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(⊥, ∧(⊥, ⊤), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(⊥, ∧(α, ⊥), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(⊥, ∧(α, α), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(⊥, ∧(α, β), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(⊥, ∧(α, ⊤), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(⊥, ∧(β, ⊥), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(⊥, ∧(β, α), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(⊥, ∧(β, β), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(⊥, ∧(β, ⊤), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(⊥, ∧(⊤, ⊥), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(⊥, ∧(⊤, α), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(⊥, ∧(⊤, β), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(⊥, ∧(⊤, ⊤), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true

@test mvhsalphasat(α, ∧(⊥, ⊥), FiniteHeytingAlgebra(H4), timeout=max_timeout) == false
@test mvhsalphasat(α, ∧(⊥, α), FiniteHeytingAlgebra(H4), timeout=max_timeout) == false
@test mvhsalphasat(α, ∧(⊥, β), FiniteHeytingAlgebra(H4), timeout=max_timeout) == false
@test mvhsalphasat(α, ∧(⊥, ⊤), FiniteHeytingAlgebra(H4), timeout=max_timeout) == false
@test mvhsalphasat(α, ∧(α, ⊥), FiniteHeytingAlgebra(H4), timeout=max_timeout) == false
@test mvhsalphasat(α, ∧(α, α), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(α, ∧(α, β), FiniteHeytingAlgebra(H4), timeout=max_timeout) == false
@test mvhsalphasat(α, ∧(α, ⊤), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(α, ∧(β, ⊥), FiniteHeytingAlgebra(H4), timeout=max_timeout) == false
@test mvhsalphasat(α, ∧(β, α), FiniteHeytingAlgebra(H4), timeout=max_timeout) == false
@test mvhsalphasat(α, ∧(β, β), FiniteHeytingAlgebra(H4), timeout=max_timeout) == false
@test mvhsalphasat(α, ∧(β, ⊤), FiniteHeytingAlgebra(H4), timeout=max_timeout) == false
@test mvhsalphasat(α, ∧(⊤, ⊥), FiniteHeytingAlgebra(H4), timeout=max_timeout) == false
@test mvhsalphasat(α, ∧(⊤, α), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(α, ∧(⊤, β), FiniteHeytingAlgebra(H4), timeout=max_timeout) == false
@test mvhsalphasat(α, ∧(⊤, ⊤), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true

@test mvhsalphasat(β, ∧(⊥, ⊥), FiniteHeytingAlgebra(H4), timeout=max_timeout) == false
@test mvhsalphasat(β, ∧(⊥, α), FiniteHeytingAlgebra(H4), timeout=max_timeout) == false
@test mvhsalphasat(β, ∧(⊥, β), FiniteHeytingAlgebra(H4), timeout=max_timeout) == false
@test mvhsalphasat(β, ∧(⊥, ⊤), FiniteHeytingAlgebra(H4), timeout=max_timeout) == false
@test mvhsalphasat(β, ∧(α, ⊥), FiniteHeytingAlgebra(H4), timeout=max_timeout) == false
@test mvhsalphasat(β, ∧(α, α), FiniteHeytingAlgebra(H4), timeout=max_timeout) == false
@test mvhsalphasat(β, ∧(α, β), FiniteHeytingAlgebra(H4), timeout=max_timeout) == false
@test mvhsalphasat(β, ∧(α, ⊤), FiniteHeytingAlgebra(H4), timeout=max_timeout) == false
@test mvhsalphasat(β, ∧(β, ⊥), FiniteHeytingAlgebra(H4), timeout=max_timeout) == false
@test mvhsalphasat(β, ∧(β, α), FiniteHeytingAlgebra(H4), timeout=max_timeout) == false
@test mvhsalphasat(β, ∧(β, β), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(β, ∧(β, ⊤), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(β, ∧(⊤, ⊥), FiniteHeytingAlgebra(H4), timeout=max_timeout) == false
@test mvhsalphasat(β, ∧(⊤, α), FiniteHeytingAlgebra(H4), timeout=max_timeout) == false
@test mvhsalphasat(β, ∧(⊤, β), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(β, ∧(⊤, ⊤), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true

@test mvhsalphasat(⊤, ∧(⊥, ⊥), FiniteHeytingAlgebra(H4), timeout=max_timeout) == false
@test mvhsalphasat(⊤, ∧(⊥, α), FiniteHeytingAlgebra(H4), timeout=max_timeout) == false
@test mvhsalphasat(⊤, ∧(⊥, β), FiniteHeytingAlgebra(H4), timeout=max_timeout) == false
@test mvhsalphasat(⊤, ∧(⊥, ⊤), FiniteHeytingAlgebra(H4), timeout=max_timeout) == false
@test mvhsalphasat(⊤, ∧(α, ⊥), FiniteHeytingAlgebra(H4), timeout=max_timeout) == false
@test mvhsalphasat(⊤, ∧(α, α), FiniteHeytingAlgebra(H4), timeout=max_timeout) == false
@test mvhsalphasat(⊤, ∧(α, β), FiniteHeytingAlgebra(H4), timeout=max_timeout) == false
@test mvhsalphasat(⊤, ∧(α, ⊤), FiniteHeytingAlgebra(H4), timeout=max_timeout) == false
@test mvhsalphasat(⊤, ∧(β, ⊥), FiniteHeytingAlgebra(H4), timeout=max_timeout) == false
@test mvhsalphasat(⊤, ∧(β, α), FiniteHeytingAlgebra(H4), timeout=max_timeout) == false
@test mvhsalphasat(⊤, ∧(β, β), FiniteHeytingAlgebra(H4), timeout=max_timeout) == false
@test mvhsalphasat(⊤, ∧(β, ⊤), FiniteHeytingAlgebra(H4), timeout=max_timeout) == false
@test mvhsalphasat(⊤, ∧(⊤, ⊥), FiniteHeytingAlgebra(H4), timeout=max_timeout) == false
@test mvhsalphasat(⊤, ∧(⊤, α), FiniteHeytingAlgebra(H4), timeout=max_timeout) == false
@test mvhsalphasat(⊤, ∧(⊤, β), FiniteHeytingAlgebra(H4), timeout=max_timeout) == false
@test mvhsalphasat(⊤, ∧(⊤, ⊤), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true

@test mvhsalphasat(⊥, ∧(parseformula("p"), ⊥), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(⊥, ∧(parseformula("p"), α), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(⊥, ∧(parseformula("p"), β), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(⊥, ∧(parseformula("p"), ⊤), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(α, ∧(parseformula("p"), ⊥), FiniteHeytingAlgebra(H4), timeout=max_timeout) == false
@test mvhsalphasat(α, ∧(parseformula("p"), α), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(α, ∧(parseformula("p"), β), FiniteHeytingAlgebra(H4), timeout=max_timeout) == false
@test mvhsalphasat(α, ∧(parseformula("p"), ⊤), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(β, ∧(parseformula("p"), ⊥), FiniteHeytingAlgebra(H4), timeout=max_timeout) == false
@test mvhsalphasat(β, ∧(parseformula("p"), α), FiniteHeytingAlgebra(H4), timeout=max_timeout) == false
@test mvhsalphasat(β, ∧(parseformula("p"), β), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(β, ∧(parseformula("p"), ⊤), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(⊤, ∧(parseformula("p"), ⊥), FiniteHeytingAlgebra(H4), timeout=max_timeout) == false
@test mvhsalphasat(⊤, ∧(parseformula("p"), α), FiniteHeytingAlgebra(H4), timeout=max_timeout) == false
@test mvhsalphasat(⊤, ∧(parseformula("p"), β), FiniteHeytingAlgebra(H4), timeout=max_timeout) == false
@test mvhsalphasat(⊤, ∧(parseformula("p"), ⊤), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true

@test mvhsalphasat(⊥, ∧(⊥, parseformula("p")), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(⊥, ∧(α, parseformula("p")), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(⊥, ∧(β, parseformula("p")), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(⊥, ∧(⊤, parseformula("p")), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(α, ∧(⊥, parseformula("p")), FiniteHeytingAlgebra(H4), timeout=max_timeout) == false
@test mvhsalphasat(α, ∧(α, parseformula("p")), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(α, ∧(β, parseformula("p")), FiniteHeytingAlgebra(H4), timeout=max_timeout) == false
@test mvhsalphasat(α, ∧(⊤, parseformula("p")), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(β, ∧(⊥, parseformula("p")), FiniteHeytingAlgebra(H4), timeout=max_timeout) == false
@test mvhsalphasat(β, ∧(α, parseformula("p")), FiniteHeytingAlgebra(H4), timeout=max_timeout) == false
@test mvhsalphasat(β, ∧(β, parseformula("p")), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(β, ∧(⊤, parseformula("p")), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(⊤, ∧(⊥, parseformula("p")), FiniteHeytingAlgebra(H4), timeout=max_timeout) == false
@test mvhsalphasat(⊤, ∧(α, parseformula("p")), FiniteHeytingAlgebra(H4), timeout=max_timeout) == false
@test mvhsalphasat(⊤, ∧(β, parseformula("p")), FiniteHeytingAlgebra(H4), timeout=max_timeout) == false
@test mvhsalphasat(⊤, ∧(⊤, parseformula("p")), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true

@test mvhsalphasat(⊥, ∧(parseformula("p"), parseformula("p")), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(α, ∧(parseformula("p"), parseformula("p")), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(β, ∧(parseformula("p"), parseformula("p")), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(⊤, ∧(parseformula("p"), parseformula("p")), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true

@test mvhsalphasat(⊥, ∧(parseformula("p"), parseformula("q")), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(α, ∧(parseformula("p"), parseformula("q")), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(β, ∧(parseformula("p"), parseformula("q")), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(⊤, ∧(parseformula("p"), parseformula("q")), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true

@test mvhsalphasat(⊥, ∧(parseformula("q"), parseformula("p")), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(α, ∧(parseformula("q"), parseformula("p")), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(β, ∧(parseformula("q"), parseformula("p")), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(⊤, ∧(parseformula("q"), parseformula("p")), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true

############################################################################################
## Implication #############################################################################
############################################################################################

@test mvhsalphasat(⊥, →(⊥, ⊥), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(⊥, →(⊥, α), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(⊥, →(⊥, β), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(⊥, →(⊥, ⊤), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(⊥, →(α, ⊥), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(⊥, →(α, α), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(⊥, →(α, β), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(⊥, →(α, ⊤), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(⊥, →(β, ⊥), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(⊥, →(β, α), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(⊥, →(β, β), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(⊥, →(β, ⊤), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(⊥, →(⊤, ⊥), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(⊥, →(⊤, α), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(⊥, →(⊤, β), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(⊥, →(⊤, ⊤), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true

@test mvhsalphasat(α, →(⊥, ⊥), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(α, →(⊥, α), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(α, →(⊥, β), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(α, →(⊥, ⊤), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(α, →(α, ⊥), FiniteHeytingAlgebra(H4), timeout=max_timeout) == false
@test mvhsalphasat(α, →(α, α), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(α, →(α, β), FiniteHeytingAlgebra(H4), timeout=max_timeout) == false
@test mvhsalphasat(α, →(α, ⊤), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(α, →(β, ⊥), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(α, →(β, α), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(α, →(β, β), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(α, →(β, ⊤), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(α, →(⊤, ⊥), FiniteHeytingAlgebra(H4), timeout=max_timeout) == false
@test mvhsalphasat(α, →(⊤, α), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(α, →(⊤, β), FiniteHeytingAlgebra(H4), timeout=max_timeout) == false
@test mvhsalphasat(α, →(⊤, ⊤), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true

@test mvhsalphasat(β, →(⊥, ⊥), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(β, →(⊥, α), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(β, →(⊥, β), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(β, →(⊥, ⊤), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(β, →(α, ⊥), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(β, →(α, α), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(β, →(α, β), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(β, →(α, ⊤), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(β, →(β, ⊥), FiniteHeytingAlgebra(H4), timeout=max_timeout) == false
@test mvhsalphasat(β, →(β, α), FiniteHeytingAlgebra(H4), timeout=max_timeout) == false
@test mvhsalphasat(β, →(β, β), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(β, →(β, ⊤), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(β, →(⊤, ⊥), FiniteHeytingAlgebra(H4), timeout=max_timeout) == false
@test mvhsalphasat(β, →(⊤, α), FiniteHeytingAlgebra(H4), timeout=max_timeout) == false
@test mvhsalphasat(β, →(⊤, β), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(β, →(⊤, ⊤), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true

@test mvhsalphasat(⊤, →(⊥, ⊥), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(⊤, →(⊥, α), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(⊤, →(⊥, β), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(⊤, →(⊥, ⊤), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(⊤, →(α, ⊥), FiniteHeytingAlgebra(H4), timeout=max_timeout) == false
@test mvhsalphasat(⊤, →(α, α), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(⊤, →(α, β), FiniteHeytingAlgebra(H4), timeout=max_timeout) == false
@test mvhsalphasat(⊤, →(α, ⊤), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(⊤, →(β, ⊥), FiniteHeytingAlgebra(H4), timeout=max_timeout) == false
@test mvhsalphasat(⊤, →(β, α), FiniteHeytingAlgebra(H4), timeout=max_timeout) == false
@test mvhsalphasat(⊤, →(β, β), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(⊤, →(β, ⊤), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(⊤, →(⊤, ⊥), FiniteHeytingAlgebra(H4), timeout=max_timeout) == false
@test mvhsalphasat(⊤, →(⊤, α), FiniteHeytingAlgebra(H4), timeout=max_timeout) == false
@test mvhsalphasat(⊤, →(⊤, β), FiniteHeytingAlgebra(H4), timeout=max_timeout) == false
@test mvhsalphasat(⊤, →(⊤, ⊤), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true

@test mvhsalphasat(⊥, →(parseformula("p"), ⊥), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(⊥, →(parseformula("p"), α), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(⊥, →(parseformula("p"), β), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(⊥, →(parseformula("p"), ⊤), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(α, →(parseformula("p"), ⊥), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(α, →(parseformula("p"), α), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(α, →(parseformula("p"), β), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(α, →(parseformula("p"), ⊤), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(β, →(parseformula("p"), ⊥), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(β, →(parseformula("p"), α), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(β, →(parseformula("p"), β), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(β, →(parseformula("p"), ⊤), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(⊤, →(parseformula("p"), ⊥), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(⊤, →(parseformula("p"), α), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(⊤, →(parseformula("p"), β), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(⊤, →(parseformula("p"), ⊤), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true

@test mvhsalphasat(⊥, →(⊥, parseformula("p")), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(⊥, →(α, parseformula("p")), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(⊥, →(β, parseformula("p")), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(⊥, →(⊤, parseformula("p")), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(α, →(⊥, parseformula("p")), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(α, →(α, parseformula("p")), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(α, →(β, parseformula("p")), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(α, →(⊤, parseformula("p")), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(β, →(⊥, parseformula("p")), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(β, →(α, parseformula("p")), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(β, →(β, parseformula("p")), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(β, →(⊤, parseformula("p")), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(⊤, →(⊥, parseformula("p")), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(⊤, →(α, parseformula("p")), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(⊤, →(β, parseformula("p")), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(⊤, →(⊤, parseformula("p")), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true

@test mvhsalphasat(⊥, →(parseformula("p"), parseformula("p")), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(α, →(parseformula("p"), parseformula("p")), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(β, →(parseformula("p"), parseformula("p")), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(⊤, →(parseformula("p"), parseformula("p")), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true

@test mvhsalphasat(⊥, →(parseformula("p"), parseformula("q")), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(α, →(parseformula("p"), parseformula("q")), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(β, →(parseformula("p"), parseformula("q")), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(⊤, →(parseformula("p"), parseformula("q")), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true

@test mvhsalphasat(⊥, →(parseformula("q"), parseformula("p")), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(α, →(parseformula("q"), parseformula("p")), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(β, →(parseformula("q"), parseformula("p")), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphasat(⊤, →(parseformula("q"), parseformula("p")), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true

############################################################################################
# FLew Algebra #############################################################################
############################################################################################
## Base cases ##############################################################################
############################################################################################
@test mvhsalphasat(⊥, ⊥, H4, timeout=max_timeout) == true
@test mvhsalphasat(⊥, α, H4, timeout=max_timeout) == true
@test mvhsalphasat(⊥, β, H4, timeout=max_timeout) == true
@test mvhsalphasat(⊥, ⊤, H4, timeout=max_timeout) == true

@test mvhsalphasat(α, ⊥, H4, timeout=max_timeout) == false
@test mvhsalphasat(α, α, H4, timeout=max_timeout) == true
@test mvhsalphasat(α, β, H4, timeout=max_timeout) == false
@test mvhsalphasat(α, ⊤, H4, timeout=max_timeout) == true

@test mvhsalphasat(β, ⊥, H4, timeout=max_timeout) == false
@test mvhsalphasat(β, α, H4, timeout=max_timeout) == false
@test mvhsalphasat(β, β, H4, timeout=max_timeout) == true
@test mvhsalphasat(β, ⊤, H4, timeout=max_timeout) == true

@test mvhsalphasat(⊤, ⊥, H4, timeout=max_timeout) == false
@test mvhsalphasat(⊤, α, H4, timeout=max_timeout) == false
@test mvhsalphasat(⊤, β, H4, timeout=max_timeout) == false
@test mvhsalphasat(⊤, ⊤, H4, timeout=max_timeout) == true

@test mvhsalphasat(⊥, parseformula("p"), H4, timeout=max_timeout) == true
@test mvhsalphasat(α, parseformula("p"), H4, timeout=max_timeout) == true
@test mvhsalphasat(β, parseformula("p"), H4, timeout=max_timeout) == true
@test mvhsalphasat(⊤, parseformula("p"), H4, timeout=max_timeout) == true

############################################################################################
## (Strong) disjuction #####################################################################
############################################################################################

@test mvhsalphasat(⊥, ∨(⊥, ⊥), H4, timeout=max_timeout) == true
@test mvhsalphasat(⊥, ∨(⊥, α), H4, timeout=max_timeout) == true
@test mvhsalphasat(⊥, ∨(⊥, β), H4, timeout=max_timeout) == true
@test mvhsalphasat(⊥, ∨(⊥, ⊤), H4, timeout=max_timeout) == true
@test mvhsalphasat(⊥, ∨(α, ⊥), H4, timeout=max_timeout) == true
@test mvhsalphasat(⊥, ∨(α, α), H4, timeout=max_timeout) == true
@test mvhsalphasat(⊥, ∨(α, β), H4, timeout=max_timeout) == true
@test mvhsalphasat(⊥, ∨(α, ⊤), H4, timeout=max_timeout) == true
@test mvhsalphasat(⊥, ∨(β, ⊥), H4, timeout=max_timeout) == true
@test mvhsalphasat(⊥, ∨(β, α), H4, timeout=max_timeout) == true
@test mvhsalphasat(⊥, ∨(β, β), H4, timeout=max_timeout) == true
@test mvhsalphasat(⊥, ∨(β, ⊤), H4, timeout=max_timeout) == true
@test mvhsalphasat(⊥, ∨(⊤, ⊥), H4, timeout=max_timeout) == true
@test mvhsalphasat(⊥, ∨(⊤, α), H4, timeout=max_timeout) == true
@test mvhsalphasat(⊥, ∨(⊤, β), H4, timeout=max_timeout) == true
@test mvhsalphasat(⊥, ∨(⊤, ⊤), H4, timeout=max_timeout) == true

@test mvhsalphasat(α, ∨(⊥, ⊥), H4, timeout=max_timeout) == false
@test mvhsalphasat(α, ∨(⊥, α), H4, timeout=max_timeout) == true
@test mvhsalphasat(α, ∨(⊥, β), H4, timeout=max_timeout) == false
@test mvhsalphasat(α, ∨(⊥, ⊤), H4, timeout=max_timeout) == true
@test mvhsalphasat(α, ∨(α, ⊥), H4, timeout=max_timeout) == true
@test mvhsalphasat(α, ∨(α, α), H4, timeout=max_timeout) == true
@test mvhsalphasat(α, ∨(α, β), H4, timeout=max_timeout) == true
@test mvhsalphasat(α, ∨(α, ⊤), H4, timeout=max_timeout) == true
@test mvhsalphasat(α, ∨(β, ⊥), H4, timeout=max_timeout) == false
@test mvhsalphasat(α, ∨(β, α), H4, timeout=max_timeout) == true
@test mvhsalphasat(α, ∨(β, β), H4, timeout=max_timeout) == false
@test mvhsalphasat(α, ∨(β, ⊤), H4, timeout=max_timeout) == true
@test mvhsalphasat(α, ∨(⊤, ⊥), H4, timeout=max_timeout) == true
@test mvhsalphasat(α, ∨(⊤, α), H4, timeout=max_timeout) == true
@test mvhsalphasat(α, ∨(⊤, β), H4, timeout=max_timeout) == true
@test mvhsalphasat(α, ∨(⊤, ⊤), H4, timeout=max_timeout) == true

@test mvhsalphasat(β, ∨(⊥, ⊥), H4, timeout=max_timeout) == false
@test mvhsalphasat(β, ∨(⊥, α), H4, timeout=max_timeout) == false
@test mvhsalphasat(β, ∨(⊥, β), H4, timeout=max_timeout) == true
@test mvhsalphasat(β, ∨(⊥, ⊤), H4, timeout=max_timeout) == true
@test mvhsalphasat(β, ∨(α, ⊥), H4, timeout=max_timeout) == false
@test mvhsalphasat(β, ∨(α, α), H4, timeout=max_timeout) == false
@test mvhsalphasat(β, ∨(α, β), H4, timeout=max_timeout) == true
@test mvhsalphasat(β, ∨(α, ⊤), H4, timeout=max_timeout) == true
@test mvhsalphasat(β, ∨(β, ⊥), H4, timeout=max_timeout) == true
@test mvhsalphasat(β, ∨(β, α), H4, timeout=max_timeout) == true
@test mvhsalphasat(β, ∨(β, β), H4, timeout=max_timeout) == true
@test mvhsalphasat(β, ∨(β, ⊤), H4, timeout=max_timeout) == true
@test mvhsalphasat(β, ∨(⊤, ⊥), H4, timeout=max_timeout) == true
@test mvhsalphasat(β, ∨(⊤, α), H4, timeout=max_timeout) == true
@test mvhsalphasat(β, ∨(⊤, β), H4, timeout=max_timeout) == true
@test mvhsalphasat(β, ∨(⊤, ⊤), H4, timeout=max_timeout) == true

@test mvhsalphasat(⊤, ∨(⊥, ⊥), H4, timeout=max_timeout) == false
@test mvhsalphasat(⊤, ∨(⊥, α), H4, timeout=max_timeout) == false
@test mvhsalphasat(⊤, ∨(⊥, β), H4, timeout=max_timeout) == false
@test mvhsalphasat(⊤, ∨(⊥, ⊤), H4, timeout=max_timeout) == true
@test mvhsalphasat(⊤, ∨(α, ⊥), H4, timeout=max_timeout) == false
@test mvhsalphasat(⊤, ∨(α, α), H4, timeout=max_timeout) == false
@test mvhsalphasat(⊤, ∨(α, β), H4, timeout=max_timeout) == true
@test mvhsalphasat(⊤, ∨(α, ⊤), H4, timeout=max_timeout) == true
@test mvhsalphasat(⊤, ∨(β, ⊥), H4, timeout=max_timeout) == false
@test mvhsalphasat(⊤, ∨(β, α), H4, timeout=max_timeout) == true
@test mvhsalphasat(⊤, ∨(β, β), H4, timeout=max_timeout) == false
@test mvhsalphasat(⊤, ∨(β, ⊤), H4, timeout=max_timeout) == true
@test mvhsalphasat(⊤, ∨(⊤, ⊥), H4, timeout=max_timeout) == true
@test mvhsalphasat(⊤, ∨(⊤, α), H4, timeout=max_timeout) == true
@test mvhsalphasat(⊤, ∨(⊤, β), H4, timeout=max_timeout) == true
@test mvhsalphasat(⊤, ∨(⊤, ⊤), H4, timeout=max_timeout) == true

@test mvhsalphasat(⊥, ∨(parseformula("p"), ⊥), H4, timeout=max_timeout) == true
@test mvhsalphasat(⊥, ∨(parseformula("p"), α), H4, timeout=max_timeout) == true
@test mvhsalphasat(⊥, ∨(parseformula("p"), β), H4, timeout=max_timeout) == true
@test mvhsalphasat(⊥, ∨(parseformula("p"), ⊤), H4, timeout=max_timeout) == true
@test mvhsalphasat(α, ∨(parseformula("p"), ⊥), H4, timeout=max_timeout) == true
@test mvhsalphasat(α, ∨(parseformula("p"), α), H4, timeout=max_timeout) == true
@test mvhsalphasat(α, ∨(parseformula("p"), β), H4, timeout=max_timeout) == true
@test mvhsalphasat(α, ∨(parseformula("p"), ⊤), H4, timeout=max_timeout) == true
@test mvhsalphasat(β, ∨(parseformula("p"), ⊥), H4, timeout=max_timeout) == true
@test mvhsalphasat(β, ∨(parseformula("p"), α), H4, timeout=max_timeout) == true
@test mvhsalphasat(β, ∨(parseformula("p"), β), H4, timeout=max_timeout) == true
@test mvhsalphasat(β, ∨(parseformula("p"), ⊤), H4, timeout=max_timeout) == true
@test mvhsalphasat(⊤, ∨(parseformula("p"), ⊥), H4, timeout=max_timeout) == true
@test mvhsalphasat(⊤, ∨(parseformula("p"), α), H4, timeout=max_timeout) == true
@test mvhsalphasat(⊤, ∨(parseformula("p"), β), H4, timeout=max_timeout) == true
@test mvhsalphasat(⊤, ∨(parseformula("p"), ⊤), H4, timeout=max_timeout) == true

@test mvhsalphasat(⊥, ∨(⊥, parseformula("p")), H4, timeout=max_timeout) == true
@test mvhsalphasat(⊥, ∨(α, parseformula("p")), H4, timeout=max_timeout) == true
@test mvhsalphasat(⊥, ∨(β, parseformula("p")), H4, timeout=max_timeout) == true
@test mvhsalphasat(⊥, ∨(⊤, parseformula("p")), H4, timeout=max_timeout) == true
@test mvhsalphasat(α, ∨(⊥, parseformula("p")), H4, timeout=max_timeout) == true
@test mvhsalphasat(α, ∨(α, parseformula("p")), H4, timeout=max_timeout) == true
@test mvhsalphasat(α, ∨(β, parseformula("p")), H4, timeout=max_timeout) == true
@test mvhsalphasat(α, ∨(⊤, parseformula("p")), H4, timeout=max_timeout) == true
@test mvhsalphasat(β, ∨(⊥, parseformula("p")), H4, timeout=max_timeout) == true
@test mvhsalphasat(β, ∨(α, parseformula("p")), H4, timeout=max_timeout) == true
@test mvhsalphasat(β, ∨(β, parseformula("p")), H4, timeout=max_timeout) == true
@test mvhsalphasat(β, ∨(⊤, parseformula("p")), H4, timeout=max_timeout) == true
@test mvhsalphasat(⊤, ∨(⊥, parseformula("p")), H4, timeout=max_timeout) == true
@test mvhsalphasat(⊤, ∨(α, parseformula("p")), H4, timeout=max_timeout) == true
@test mvhsalphasat(⊤, ∨(β, parseformula("p")), H4, timeout=max_timeout) == true
@test mvhsalphasat(⊤, ∨(⊤, parseformula("p")), H4, timeout=max_timeout) == true

@test mvhsalphasat(⊥, ∨(parseformula("p"), parseformula("p")), H4, timeout=max_timeout) == true
@test mvhsalphasat(α, ∨(parseformula("p"), parseformula("p")), H4, timeout=max_timeout) == true
@test mvhsalphasat(β, ∨(parseformula("p"), parseformula("p")), H4, timeout=max_timeout) == true
@test mvhsalphasat(⊤, ∨(parseformula("p"), parseformula("p")), H4, timeout=max_timeout) == true

@test mvhsalphasat(⊥, ∨(parseformula("p"), parseformula("q")), H4, timeout=max_timeout) == true
@test mvhsalphasat(α, ∨(parseformula("p"), parseformula("q")), H4, timeout=max_timeout) == true
@test mvhsalphasat(β, ∨(parseformula("p"), parseformula("q")), H4, timeout=max_timeout) == true
@test mvhsalphasat(⊤, ∨(parseformula("p"), parseformula("q")), H4, timeout=max_timeout) == true

@test mvhsalphasat(⊥, ∨(parseformula("q"), parseformula("q")), H4, timeout=max_timeout) == true
@test mvhsalphasat(α, ∨(parseformula("q"), parseformula("q")), H4, timeout=max_timeout) == true
@test mvhsalphasat(β, ∨(parseformula("q"), parseformula("q")), H4, timeout=max_timeout) == true
@test mvhsalphasat(⊤, ∨(parseformula("q"), parseformula("q")), H4, timeout=max_timeout) == true

############################################################################################
## (Strong) conjunction ####################################################################
############################################################################################

@test mvhsalphasat(⊥, ∧(⊥, ⊥), H4, timeout=max_timeout) == true
@test mvhsalphasat(⊥, ∧(⊥, α), H4, timeout=max_timeout) == true
@test mvhsalphasat(⊥, ∧(⊥, β), H4, timeout=max_timeout) == true
@test mvhsalphasat(⊥, ∧(⊥, ⊤), H4, timeout=max_timeout) == true
@test mvhsalphasat(⊥, ∧(α, ⊥), H4, timeout=max_timeout) == true
@test mvhsalphasat(⊥, ∧(α, α), H4, timeout=max_timeout) == true
@test mvhsalphasat(⊥, ∧(α, β), H4, timeout=max_timeout) == true
@test mvhsalphasat(⊥, ∧(α, ⊤), H4, timeout=max_timeout) == true
@test mvhsalphasat(⊥, ∧(β, ⊥), H4, timeout=max_timeout) == true
@test mvhsalphasat(⊥, ∧(β, α), H4, timeout=max_timeout) == true
@test mvhsalphasat(⊥, ∧(β, β), H4, timeout=max_timeout) == true
@test mvhsalphasat(⊥, ∧(β, ⊤), H4, timeout=max_timeout) == true
@test mvhsalphasat(⊥, ∧(⊤, ⊥), H4, timeout=max_timeout) == true
@test mvhsalphasat(⊥, ∧(⊤, α), H4, timeout=max_timeout) == true
@test mvhsalphasat(⊥, ∧(⊤, β), H4, timeout=max_timeout) == true
@test mvhsalphasat(⊥, ∧(⊤, ⊤), H4, timeout=max_timeout) == true

@test mvhsalphasat(α, ∧(⊥, ⊥), H4, timeout=max_timeout) == false
@test mvhsalphasat(α, ∧(⊥, α), H4, timeout=max_timeout) == false
@test mvhsalphasat(α, ∧(⊥, β), H4, timeout=max_timeout) == false
@test mvhsalphasat(α, ∧(⊥, ⊤), H4, timeout=max_timeout) == false
@test mvhsalphasat(α, ∧(α, ⊥), H4, timeout=max_timeout) == false
@test mvhsalphasat(α, ∧(α, α), H4, timeout=max_timeout) == true
@test mvhsalphasat(α, ∧(α, β), H4, timeout=max_timeout) == false
@test mvhsalphasat(α, ∧(α, ⊤), H4, timeout=max_timeout) == true
@test mvhsalphasat(α, ∧(β, ⊥), H4, timeout=max_timeout) == false
@test mvhsalphasat(α, ∧(β, α), H4, timeout=max_timeout) == false
@test mvhsalphasat(α, ∧(β, β), H4, timeout=max_timeout) == false
@test mvhsalphasat(α, ∧(β, ⊤), H4, timeout=max_timeout) == false
@test mvhsalphasat(α, ∧(⊤, ⊥), H4, timeout=max_timeout) == false
@test mvhsalphasat(α, ∧(⊤, α), H4, timeout=max_timeout) == true
@test mvhsalphasat(α, ∧(⊤, β), H4, timeout=max_timeout) == false
@test mvhsalphasat(α, ∧(⊤, ⊤), H4, timeout=max_timeout) == true

@test mvhsalphasat(β, ∧(⊥, ⊥), H4, timeout=max_timeout) == false
@test mvhsalphasat(β, ∧(⊥, α), H4, timeout=max_timeout) == false
@test mvhsalphasat(β, ∧(⊥, β), H4, timeout=max_timeout) == false
@test mvhsalphasat(β, ∧(⊥, ⊤), H4, timeout=max_timeout) == false
@test mvhsalphasat(β, ∧(α, ⊥), H4, timeout=max_timeout) == false
@test mvhsalphasat(β, ∧(α, α), H4, timeout=max_timeout) == false
@test mvhsalphasat(β, ∧(α, β), H4, timeout=max_timeout) == false
@test mvhsalphasat(β, ∧(α, ⊤), H4, timeout=max_timeout) == false
@test mvhsalphasat(β, ∧(β, ⊥), H4, timeout=max_timeout) == false
@test mvhsalphasat(β, ∧(β, α), H4, timeout=max_timeout) == false
@test mvhsalphasat(β, ∧(β, β), H4, timeout=max_timeout) == true
@test mvhsalphasat(β, ∧(β, ⊤), H4, timeout=max_timeout) == true
@test mvhsalphasat(β, ∧(⊤, ⊥), H4, timeout=max_timeout) == false
@test mvhsalphasat(β, ∧(⊤, α), H4, timeout=max_timeout) == false
@test mvhsalphasat(β, ∧(⊤, β), H4, timeout=max_timeout) == true
@test mvhsalphasat(β, ∧(⊤, ⊤), H4, timeout=max_timeout) == true

@test mvhsalphasat(⊤, ∧(⊥, ⊥), H4, timeout=max_timeout) == false
@test mvhsalphasat(⊤, ∧(⊥, α), H4, timeout=max_timeout) == false
@test mvhsalphasat(⊤, ∧(⊥, β), H4, timeout=max_timeout) == false
@test mvhsalphasat(⊤, ∧(⊥, ⊤), H4, timeout=max_timeout) == false
@test mvhsalphasat(⊤, ∧(α, ⊥), H4, timeout=max_timeout) == false
@test mvhsalphasat(⊤, ∧(α, α), H4, timeout=max_timeout) == false
@test mvhsalphasat(⊤, ∧(α, β), H4, timeout=max_timeout) == false
@test mvhsalphasat(⊤, ∧(α, ⊤), H4, timeout=max_timeout) == false
@test mvhsalphasat(⊤, ∧(β, ⊥), H4, timeout=max_timeout) == false
@test mvhsalphasat(⊤, ∧(β, α), H4, timeout=max_timeout) == false
@test mvhsalphasat(⊤, ∧(β, β), H4, timeout=max_timeout) == false
@test mvhsalphasat(⊤, ∧(β, ⊤), H4, timeout=max_timeout) == false
@test mvhsalphasat(⊤, ∧(⊤, ⊥), H4, timeout=max_timeout) == false
@test mvhsalphasat(⊤, ∧(⊤, α), H4, timeout=max_timeout) == false
@test mvhsalphasat(⊤, ∧(⊤, β), H4, timeout=max_timeout) == false
@test mvhsalphasat(⊤, ∧(⊤, ⊤), H4, timeout=max_timeout) == true

@test mvhsalphasat(⊥, ∧(parseformula("p"), ⊥), H4, timeout=max_timeout) == true
@test mvhsalphasat(⊥, ∧(parseformula("p"), α), H4, timeout=max_timeout) == true
@test mvhsalphasat(⊥, ∧(parseformula("p"), β), H4, timeout=max_timeout) == true
@test mvhsalphasat(⊥, ∧(parseformula("p"), ⊤), H4, timeout=max_timeout) == true
@test mvhsalphasat(α, ∧(parseformula("p"), ⊥), H4, timeout=max_timeout) == false
@test mvhsalphasat(α, ∧(parseformula("p"), α), H4, timeout=max_timeout) == true
@test mvhsalphasat(α, ∧(parseformula("p"), β), H4, timeout=max_timeout) == false
@test mvhsalphasat(α, ∧(parseformula("p"), ⊤), H4, timeout=max_timeout) == true
@test mvhsalphasat(β, ∧(parseformula("p"), ⊥), H4, timeout=max_timeout) == false
@test mvhsalphasat(β, ∧(parseformula("p"), α), H4, timeout=max_timeout) == false
@test mvhsalphasat(β, ∧(parseformula("p"), β), H4, timeout=max_timeout) == true
@test mvhsalphasat(β, ∧(parseformula("p"), ⊤), H4, timeout=max_timeout) == true
@test mvhsalphasat(⊤, ∧(parseformula("p"), ⊥), H4, timeout=max_timeout) == false
@test mvhsalphasat(⊤, ∧(parseformula("p"), α), H4, timeout=max_timeout) == false
@test mvhsalphasat(⊤, ∧(parseformula("p"), β), H4, timeout=max_timeout) == false
@test mvhsalphasat(⊤, ∧(parseformula("p"), ⊤), H4, timeout=max_timeout) == true

@test mvhsalphasat(⊥, ∧(⊥, parseformula("p")), H4, timeout=max_timeout) == true
@test mvhsalphasat(⊥, ∧(α, parseformula("p")), H4, timeout=max_timeout) == true
@test mvhsalphasat(⊥, ∧(β, parseformula("p")), H4, timeout=max_timeout) == true
@test mvhsalphasat(⊥, ∧(⊤, parseformula("p")), H4, timeout=max_timeout) == true
@test mvhsalphasat(α, ∧(⊥, parseformula("p")), H4, timeout=max_timeout) == false
@test mvhsalphasat(α, ∧(α, parseformula("p")), H4, timeout=max_timeout) == true
@test mvhsalphasat(α, ∧(β, parseformula("p")), H4, timeout=max_timeout) == false
@test mvhsalphasat(α, ∧(⊤, parseformula("p")), H4, timeout=max_timeout) == true
@test mvhsalphasat(β, ∧(⊥, parseformula("p")), H4, timeout=max_timeout) == false
@test mvhsalphasat(β, ∧(α, parseformula("p")), H4, timeout=max_timeout) == false
@test mvhsalphasat(β, ∧(β, parseformula("p")), H4, timeout=max_timeout) == true
@test mvhsalphasat(β, ∧(⊤, parseformula("p")), H4, timeout=max_timeout) == true
@test mvhsalphasat(⊤, ∧(⊥, parseformula("p")), H4, timeout=max_timeout) == false
@test mvhsalphasat(⊤, ∧(α, parseformula("p")), H4, timeout=max_timeout) == false
@test mvhsalphasat(⊤, ∧(β, parseformula("p")), H4, timeout=max_timeout) == false
@test mvhsalphasat(⊤, ∧(⊤, parseformula("p")), H4, timeout=max_timeout) == true

@test mvhsalphasat(⊥, ∧(parseformula("p"), parseformula("p")), H4, timeout=max_timeout) == true
@test mvhsalphasat(α, ∧(parseformula("p"), parseformula("p")), H4, timeout=max_timeout) == true
@test mvhsalphasat(β, ∧(parseformula("p"), parseformula("p")), H4, timeout=max_timeout) == true
@test mvhsalphasat(⊤, ∧(parseformula("p"), parseformula("p")), H4, timeout=max_timeout) == true

@test mvhsalphasat(⊥, ∧(parseformula("p"), parseformula("q")), H4, timeout=max_timeout) == true
@test mvhsalphasat(α, ∧(parseformula("p"), parseformula("q")), H4, timeout=max_timeout) == true
@test mvhsalphasat(β, ∧(parseformula("p"), parseformula("q")), H4, timeout=max_timeout) == true
@test mvhsalphasat(⊤, ∧(parseformula("p"), parseformula("q")), H4, timeout=max_timeout) == true

@test mvhsalphasat(⊥, ∧(parseformula("q"), parseformula("p")), H4, timeout=max_timeout) == true
@test mvhsalphasat(α, ∧(parseformula("q"), parseformula("p")), H4, timeout=max_timeout) == true
@test mvhsalphasat(β, ∧(parseformula("q"), parseformula("p")), H4, timeout=max_timeout) == true
@test mvhsalphasat(⊤, ∧(parseformula("q"), parseformula("p")), H4, timeout=max_timeout) == true

############################################################################################
## Implication #############################################################################
############################################################################################

@test mvhsalphasat(⊥, →(⊥, ⊥), H4, timeout=max_timeout) == true
@test mvhsalphasat(⊥, →(⊥, α), H4, timeout=max_timeout) == true
@test mvhsalphasat(⊥, →(⊥, β), H4, timeout=max_timeout) == true
@test mvhsalphasat(⊥, →(⊥, ⊤), H4, timeout=max_timeout) == true
@test mvhsalphasat(⊥, →(α, ⊥), H4, timeout=max_timeout) == true
@test mvhsalphasat(⊥, →(α, α), H4, timeout=max_timeout) == true
@test mvhsalphasat(⊥, →(α, β), H4, timeout=max_timeout) == true
@test mvhsalphasat(⊥, →(α, ⊤), H4, timeout=max_timeout) == true
@test mvhsalphasat(⊥, →(β, ⊥), H4, timeout=max_timeout) == true
@test mvhsalphasat(⊥, →(β, α), H4, timeout=max_timeout) == true
@test mvhsalphasat(⊥, →(β, β), H4, timeout=max_timeout) == true
@test mvhsalphasat(⊥, →(β, ⊤), H4, timeout=max_timeout) == true
@test mvhsalphasat(⊥, →(⊤, ⊥), H4, timeout=max_timeout) == true
@test mvhsalphasat(⊥, →(⊤, α), H4, timeout=max_timeout) == true
@test mvhsalphasat(⊥, →(⊤, β), H4, timeout=max_timeout) == true
@test mvhsalphasat(⊥, →(⊤, ⊤), H4, timeout=max_timeout) == true

@test mvhsalphasat(α, →(⊥, ⊥), H4, timeout=max_timeout) == true
@test mvhsalphasat(α, →(⊥, α), H4, timeout=max_timeout) == true
@test mvhsalphasat(α, →(⊥, β), H4, timeout=max_timeout) == true
@test mvhsalphasat(α, →(⊥, ⊤), H4, timeout=max_timeout) == true
@test mvhsalphasat(α, →(α, ⊥), H4, timeout=max_timeout) == false
@test mvhsalphasat(α, →(α, α), H4, timeout=max_timeout) == true
@test mvhsalphasat(α, →(α, β), H4, timeout=max_timeout) == false
@test mvhsalphasat(α, →(α, ⊤), H4, timeout=max_timeout) == true
@test mvhsalphasat(α, →(β, ⊥), H4, timeout=max_timeout) == true
@test mvhsalphasat(α, →(β, α), H4, timeout=max_timeout) == true
@test mvhsalphasat(α, →(β, β), H4, timeout=max_timeout) == true
@test mvhsalphasat(α, →(β, ⊤), H4, timeout=max_timeout) == true
@test mvhsalphasat(α, →(⊤, ⊥), H4, timeout=max_timeout) == false
@test mvhsalphasat(α, →(⊤, α), H4, timeout=max_timeout) == true
@test mvhsalphasat(α, →(⊤, β), H4, timeout=max_timeout) == false
@test mvhsalphasat(α, →(⊤, ⊤), H4, timeout=max_timeout) == true

@test mvhsalphasat(β, →(⊥, ⊥), H4, timeout=max_timeout) == true
@test mvhsalphasat(β, →(⊥, α), H4, timeout=max_timeout) == true
@test mvhsalphasat(β, →(⊥, β), H4, timeout=max_timeout) == true
@test mvhsalphasat(β, →(⊥, ⊤), H4, timeout=max_timeout) == true
@test mvhsalphasat(β, →(α, ⊥), H4, timeout=max_timeout) == true
@test mvhsalphasat(β, →(α, α), H4, timeout=max_timeout) == true
@test mvhsalphasat(β, →(α, β), H4, timeout=max_timeout) == true
@test mvhsalphasat(β, →(α, ⊤), H4, timeout=max_timeout) == true
@test mvhsalphasat(β, →(β, ⊥), H4, timeout=max_timeout) == false
@test mvhsalphasat(β, →(β, α), H4, timeout=max_timeout) == false
@test mvhsalphasat(β, →(β, β), H4, timeout=max_timeout) == true
@test mvhsalphasat(β, →(β, ⊤), H4, timeout=max_timeout) == true
@test mvhsalphasat(β, →(⊤, ⊥), H4, timeout=max_timeout) == false
@test mvhsalphasat(β, →(⊤, α), H4, timeout=max_timeout) == false
@test mvhsalphasat(β, →(⊤, β), H4, timeout=max_timeout) == true
@test mvhsalphasat(β, →(⊤, ⊤), H4, timeout=max_timeout) == true

@test mvhsalphasat(⊤, →(⊥, ⊥), H4, timeout=max_timeout) == true
@test mvhsalphasat(⊤, →(⊥, α), H4, timeout=max_timeout) == true
@test mvhsalphasat(⊤, →(⊥, β), H4, timeout=max_timeout) == true
@test mvhsalphasat(⊤, →(⊥, ⊤), H4, timeout=max_timeout) == true
@test mvhsalphasat(⊤, →(α, ⊥), H4, timeout=max_timeout) == false
@test mvhsalphasat(⊤, →(α, α), H4, timeout=max_timeout) == true
@test mvhsalphasat(⊤, →(α, β), H4, timeout=max_timeout) == false
@test mvhsalphasat(⊤, →(α, ⊤), H4, timeout=max_timeout) == true
@test mvhsalphasat(⊤, →(β, ⊥), H4, timeout=max_timeout) == false
@test mvhsalphasat(⊤, →(β, α), H4, timeout=max_timeout) == false
@test mvhsalphasat(⊤, →(β, β), H4, timeout=max_timeout) == true
@test mvhsalphasat(⊤, →(β, ⊤), H4, timeout=max_timeout) == true
@test mvhsalphasat(⊤, →(⊤, ⊥), H4, timeout=max_timeout) == false
@test mvhsalphasat(⊤, →(⊤, α), H4, timeout=max_timeout) == false
@test mvhsalphasat(⊤, →(⊤, β), H4, timeout=max_timeout) == false
@test mvhsalphasat(⊤, →(⊤, ⊤), H4, timeout=max_timeout) == true

@test mvhsalphasat(⊥, →(parseformula("p"), ⊥), H4, timeout=max_timeout) == true
@test mvhsalphasat(⊥, →(parseformula("p"), α), H4, timeout=max_timeout) == true
@test mvhsalphasat(⊥, →(parseformula("p"), β), H4, timeout=max_timeout) == true
@test mvhsalphasat(⊥, →(parseformula("p"), ⊤), H4, timeout=max_timeout) == true
@test mvhsalphasat(α, →(parseformula("p"), ⊥), H4, timeout=max_timeout) == true
@test mvhsalphasat(α, →(parseformula("p"), α), H4, timeout=max_timeout) == true
@test mvhsalphasat(α, →(parseformula("p"), β), H4, timeout=max_timeout) == true
@test mvhsalphasat(α, →(parseformula("p"), ⊤), H4, timeout=max_timeout) == true
@test mvhsalphasat(β, →(parseformula("p"), ⊥), H4, timeout=max_timeout) == true
@test mvhsalphasat(β, →(parseformula("p"), α), H4, timeout=max_timeout) == true
@test mvhsalphasat(β, →(parseformula("p"), β), H4, timeout=max_timeout) == true
@test mvhsalphasat(β, →(parseformula("p"), ⊤), H4, timeout=max_timeout) == true
@test mvhsalphasat(⊤, →(parseformula("p"), ⊥), H4, timeout=max_timeout) == true
@test mvhsalphasat(⊤, →(parseformula("p"), α), H4, timeout=max_timeout) == true
@test mvhsalphasat(⊤, →(parseformula("p"), β), H4, timeout=max_timeout) == true
@test mvhsalphasat(⊤, →(parseformula("p"), ⊤), H4, timeout=max_timeout) == true

@test mvhsalphasat(⊥, →(⊥, parseformula("p")), H4, timeout=max_timeout) == true
@test mvhsalphasat(⊥, →(α, parseformula("p")), H4, timeout=max_timeout) == true
@test mvhsalphasat(⊥, →(β, parseformula("p")), H4, timeout=max_timeout) == true
@test mvhsalphasat(⊥, →(⊤, parseformula("p")), H4, timeout=max_timeout) == true
@test mvhsalphasat(α, →(⊥, parseformula("p")), H4, timeout=max_timeout) == true
@test mvhsalphasat(α, →(α, parseformula("p")), H4, timeout=max_timeout) == true
@test mvhsalphasat(α, →(β, parseformula("p")), H4, timeout=max_timeout) == true
@test mvhsalphasat(α, →(⊤, parseformula("p")), H4, timeout=max_timeout) == true
@test mvhsalphasat(β, →(⊥, parseformula("p")), H4, timeout=max_timeout) == true
@test mvhsalphasat(β, →(α, parseformula("p")), H4, timeout=max_timeout) == true
@test mvhsalphasat(β, →(β, parseformula("p")), H4, timeout=max_timeout) == true
@test mvhsalphasat(β, →(⊤, parseformula("p")), H4, timeout=max_timeout) == true
@test mvhsalphasat(⊤, →(⊥, parseformula("p")), H4, timeout=max_timeout) == true
@test mvhsalphasat(⊤, →(α, parseformula("p")), H4, timeout=max_timeout) == true
@test mvhsalphasat(⊤, →(β, parseformula("p")), H4, timeout=max_timeout) == true
@test mvhsalphasat(⊤, →(⊤, parseformula("p")), H4, timeout=max_timeout) == true

@test mvhsalphasat(⊥, →(parseformula("p"), parseformula("p")), H4, timeout=max_timeout) == true
@test mvhsalphasat(α, →(parseformula("p"), parseformula("p")), H4, timeout=max_timeout) == true
@test mvhsalphasat(β, →(parseformula("p"), parseformula("p")), H4, timeout=max_timeout) == true
@test mvhsalphasat(⊤, →(parseformula("p"), parseformula("p")), H4, timeout=max_timeout) == true

@test mvhsalphasat(⊥, →(parseformula("p"), parseformula("q")), H4, timeout=max_timeout) == true
@test mvhsalphasat(α, →(parseformula("p"), parseformula("q")), H4, timeout=max_timeout) == true
@test mvhsalphasat(β, →(parseformula("p"), parseformula("q")), H4, timeout=max_timeout) == true
@test mvhsalphasat(⊤, →(parseformula("p"), parseformula("q")), H4, timeout=max_timeout) == true

@test mvhsalphasat(⊥, →(parseformula("q"), parseformula("p")), H4, timeout=max_timeout) == true
@test mvhsalphasat(α, →(parseformula("q"), parseformula("p")), H4, timeout=max_timeout) == true
@test mvhsalphasat(β, →(parseformula("q"), parseformula("p")), H4, timeout=max_timeout) == true
@test mvhsalphasat(⊤, →(parseformula("q"), parseformula("p")), H4, timeout=max_timeout) == true
