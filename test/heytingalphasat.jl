############################################################################################
#### H4 ####################################################################################
############################################################################################

include("algebras/h4.jl")

############################################################################################
## Base cases ##############################################################################
############################################################################################

@test alphasat(⊥, ⊥, FiniteHeytingAlgebra(H4)) == true
@test alphasat(⊥, α, FiniteHeytingAlgebra(H4)) == true
@test alphasat(⊥, β, FiniteHeytingAlgebra(H4)) == true
@test alphasat(⊥, ⊤, FiniteHeytingAlgebra(H4)) == true
@test alphasat(α, ⊥, FiniteHeytingAlgebra(H4)) == false
@test alphasat(α, α, FiniteHeytingAlgebra(H4)) == true
@test alphasat(α, β, FiniteHeytingAlgebra(H4)) == false
@test alphasat(α, ⊤, FiniteHeytingAlgebra(H4)) == true
@test alphasat(β, ⊥, FiniteHeytingAlgebra(H4)) == false
@test alphasat(β, α, FiniteHeytingAlgebra(H4)) == false
@test alphasat(β, β, FiniteHeytingAlgebra(H4)) == true
@test alphasat(β, ⊤, FiniteHeytingAlgebra(H4)) == true
@test alphasat(⊤, ⊥, FiniteHeytingAlgebra(H4)) == false
@test alphasat(⊤, α, FiniteHeytingAlgebra(H4)) == false
@test alphasat(⊤, β, FiniteHeytingAlgebra(H4)) == false
@test alphasat(⊤, ⊤, FiniteHeytingAlgebra(H4)) == true

@test alphasat(⊥, parseformula("p"), FiniteHeytingAlgebra(H4)) == true
@test alphasat(α, parseformula("p"), FiniteHeytingAlgebra(H4)) == true
@test alphasat(β, parseformula("p"), FiniteHeytingAlgebra(H4)) == true
@test alphasat(⊤, parseformula("p"), FiniteHeytingAlgebra(H4)) == true

############################################################################################
## (Strong) disjuction #####################################################################
############################################################################################

@test alphasat(⊥, ∨(⊥, ⊥), FiniteHeytingAlgebra(H4)) == true
@test alphasat(⊥, ∨(⊥, α), FiniteHeytingAlgebra(H4)) == true
@test alphasat(⊥, ∨(⊥, β), FiniteHeytingAlgebra(H4)) == true
@test alphasat(⊥, ∨(⊥, ⊤), FiniteHeytingAlgebra(H4)) == true
@test alphasat(⊥, ∨(α, ⊥), FiniteHeytingAlgebra(H4)) == true
@test alphasat(⊥, ∨(α, α), FiniteHeytingAlgebra(H4)) == true
@test alphasat(⊥, ∨(α, β), FiniteHeytingAlgebra(H4)) == true
@test alphasat(⊥, ∨(α, ⊤), FiniteHeytingAlgebra(H4)) == true
@test alphasat(⊥, ∨(β, ⊥), FiniteHeytingAlgebra(H4)) == true
@test alphasat(⊥, ∨(β, α), FiniteHeytingAlgebra(H4)) == true
@test alphasat(⊥, ∨(β, β), FiniteHeytingAlgebra(H4)) == true
@test alphasat(⊥, ∨(β, ⊤), FiniteHeytingAlgebra(H4)) == true
@test alphasat(⊥, ∨(⊤, ⊥), FiniteHeytingAlgebra(H4)) == true
@test alphasat(⊥, ∨(⊤, α), FiniteHeytingAlgebra(H4)) == true
@test alphasat(⊥, ∨(⊤, β), FiniteHeytingAlgebra(H4)) == true
@test alphasat(⊥, ∨(⊤, ⊤), FiniteHeytingAlgebra(H4)) == true

@test alphasat(α, ∨(⊥, ⊥), FiniteHeytingAlgebra(H4)) == false
@test alphasat(α, ∨(⊥, α), FiniteHeytingAlgebra(H4)) == true
@test alphasat(α, ∨(⊥, β), FiniteHeytingAlgebra(H4)) == false
@test alphasat(α, ∨(⊥, ⊤), FiniteHeytingAlgebra(H4)) == true
@test alphasat(α, ∨(α, ⊥), FiniteHeytingAlgebra(H4)) == true
@test alphasat(α, ∨(α, α), FiniteHeytingAlgebra(H4)) == true
@test alphasat(α, ∨(α, β), FiniteHeytingAlgebra(H4)) == true
@test alphasat(α, ∨(α, ⊤), FiniteHeytingAlgebra(H4)) == true
@test alphasat(α, ∨(β, ⊥), FiniteHeytingAlgebra(H4)) == false
@test alphasat(α, ∨(β, α), FiniteHeytingAlgebra(H4)) == true
@test alphasat(α, ∨(β, β), FiniteHeytingAlgebra(H4)) == false
@test alphasat(α, ∨(β, ⊤), FiniteHeytingAlgebra(H4)) == true
@test alphasat(α, ∨(⊤, ⊥), FiniteHeytingAlgebra(H4)) == true
@test alphasat(α, ∨(⊤, α), FiniteHeytingAlgebra(H4)) == true
@test alphasat(α, ∨(⊤, β), FiniteHeytingAlgebra(H4)) == true
@test alphasat(α, ∨(⊤, ⊤), FiniteHeytingAlgebra(H4)) == true

@test alphasat(β, ∨(⊥, ⊥), FiniteHeytingAlgebra(H4)) == false
@test alphasat(β, ∨(⊥, α), FiniteHeytingAlgebra(H4)) == false
@test alphasat(β, ∨(⊥, β), FiniteHeytingAlgebra(H4)) == true
@test alphasat(β, ∨(⊥, ⊤), FiniteHeytingAlgebra(H4)) == true
@test alphasat(β, ∨(α, ⊥), FiniteHeytingAlgebra(H4)) == false
@test alphasat(β, ∨(α, α), FiniteHeytingAlgebra(H4)) == false
@test alphasat(β, ∨(α, β), FiniteHeytingAlgebra(H4)) == true
@test alphasat(β, ∨(α, ⊤), FiniteHeytingAlgebra(H4)) == true
@test alphasat(β, ∨(β, ⊥), FiniteHeytingAlgebra(H4)) == true
@test alphasat(β, ∨(β, α), FiniteHeytingAlgebra(H4)) == true
@test alphasat(β, ∨(β, β), FiniteHeytingAlgebra(H4)) == true
@test alphasat(β, ∨(β, ⊤), FiniteHeytingAlgebra(H4)) == true
@test alphasat(β, ∨(⊤, ⊥), FiniteHeytingAlgebra(H4)) == true
@test alphasat(β, ∨(⊤, α), FiniteHeytingAlgebra(H4)) == true
@test alphasat(β, ∨(⊤, β), FiniteHeytingAlgebra(H4)) == true
@test alphasat(β, ∨(⊤, ⊤), FiniteHeytingAlgebra(H4)) == true

@test alphasat(⊤, ∨(⊥, ⊥), FiniteHeytingAlgebra(H4)) == false
@test alphasat(⊤, ∨(⊥, α), FiniteHeytingAlgebra(H4)) == false
@test alphasat(⊤, ∨(⊥, β), FiniteHeytingAlgebra(H4)) == false
@test alphasat(⊤, ∨(⊥, ⊤), FiniteHeytingAlgebra(H4)) == true
@test alphasat(⊤, ∨(α, ⊥), FiniteHeytingAlgebra(H4)) == false
@test alphasat(⊤, ∨(α, α), FiniteHeytingAlgebra(H4)) == false
@test alphasat(⊤, ∨(α, β), FiniteHeytingAlgebra(H4)) == true
@test alphasat(⊤, ∨(α, ⊤), FiniteHeytingAlgebra(H4)) == true
@test alphasat(⊤, ∨(β, ⊥), FiniteHeytingAlgebra(H4)) == false
@test alphasat(⊤, ∨(β, α), FiniteHeytingAlgebra(H4)) == true
@test alphasat(⊤, ∨(β, β), FiniteHeytingAlgebra(H4)) == false
@test alphasat(⊤, ∨(β, ⊤), FiniteHeytingAlgebra(H4)) == true
@test alphasat(⊤, ∨(⊤, ⊥), FiniteHeytingAlgebra(H4)) == true
@test alphasat(⊤, ∨(⊤, α), FiniteHeytingAlgebra(H4)) == true
@test alphasat(⊤, ∨(⊤, β), FiniteHeytingAlgebra(H4)) == true
@test alphasat(⊤, ∨(⊤, ⊤), FiniteHeytingAlgebra(H4)) == true

@test alphasat(⊥, ∨(parseformula("p"), ⊥), FiniteHeytingAlgebra(H4)) == true
@test alphasat(⊥, ∨(parseformula("p"), α), FiniteHeytingAlgebra(H4)) == true
@test alphasat(⊥, ∨(parseformula("p"), β), FiniteHeytingAlgebra(H4)) == true
@test alphasat(⊥, ∨(parseformula("p"), ⊤), FiniteHeytingAlgebra(H4)) == true
@test alphasat(α, ∨(parseformula("p"), ⊥), FiniteHeytingAlgebra(H4)) == true
@test alphasat(α, ∨(parseformula("p"), α), FiniteHeytingAlgebra(H4)) == true
@test alphasat(α, ∨(parseformula("p"), β), FiniteHeytingAlgebra(H4)) == true
@test alphasat(α, ∨(parseformula("p"), ⊤), FiniteHeytingAlgebra(H4)) == true
@test alphasat(β, ∨(parseformula("p"), ⊥), FiniteHeytingAlgebra(H4)) == true
@test alphasat(β, ∨(parseformula("p"), α), FiniteHeytingAlgebra(H4)) == true
@test alphasat(β, ∨(parseformula("p"), β), FiniteHeytingAlgebra(H4)) == true
@test alphasat(β, ∨(parseformula("p"), ⊤), FiniteHeytingAlgebra(H4)) == true
@test alphasat(⊤, ∨(parseformula("p"), ⊥), FiniteHeytingAlgebra(H4)) == true
@test alphasat(⊤, ∨(parseformula("p"), α), FiniteHeytingAlgebra(H4)) == true
@test alphasat(⊤, ∨(parseformula("p"), β), FiniteHeytingAlgebra(H4)) == true
@test alphasat(⊤, ∨(parseformula("p"), ⊤), FiniteHeytingAlgebra(H4)) == true

@test alphasat(⊥, ∨(⊥, parseformula("p")), FiniteHeytingAlgebra(H4)) == true
@test alphasat(⊥, ∨(α, parseformula("p")), FiniteHeytingAlgebra(H4)) == true
@test alphasat(⊥, ∨(β, parseformula("p")), FiniteHeytingAlgebra(H4)) == true
@test alphasat(⊥, ∨(⊤, parseformula("p")), FiniteHeytingAlgebra(H4)) == true
@test alphasat(α, ∨(⊥, parseformula("p")), FiniteHeytingAlgebra(H4)) == true
@test alphasat(α, ∨(α, parseformula("p")), FiniteHeytingAlgebra(H4)) == true
@test alphasat(α, ∨(β, parseformula("p")), FiniteHeytingAlgebra(H4)) == true
@test alphasat(α, ∨(⊤, parseformula("p")), FiniteHeytingAlgebra(H4)) == true
@test alphasat(β, ∨(⊥, parseformula("p")), FiniteHeytingAlgebra(H4)) == true
@test alphasat(β, ∨(α, parseformula("p")), FiniteHeytingAlgebra(H4)) == true
@test alphasat(β, ∨(β, parseformula("p")), FiniteHeytingAlgebra(H4)) == true
@test alphasat(β, ∨(⊤, parseformula("p")), FiniteHeytingAlgebra(H4)) == true
@test alphasat(⊤, ∨(⊥, parseformula("p")), FiniteHeytingAlgebra(H4)) == true
@test alphasat(⊤, ∨(α, parseformula("p")), FiniteHeytingAlgebra(H4)) == true
@test alphasat(⊤, ∨(β, parseformula("p")), FiniteHeytingAlgebra(H4)) == true
@test alphasat(⊤, ∨(⊤, parseformula("p")), FiniteHeytingAlgebra(H4)) == true

@test alphasat(⊥, ∨(parseformula("p"), parseformula("p")), FiniteHeytingAlgebra(H4)) == true
@test alphasat(α, ∨(parseformula("p"), parseformula("p")), FiniteHeytingAlgebra(H4)) == true
@test alphasat(β, ∨(parseformula("p"), parseformula("p")), FiniteHeytingAlgebra(H4)) == true
@test alphasat(⊤, ∨(parseformula("p"), parseformula("p")), FiniteHeytingAlgebra(H4)) == true

@test alphasat(⊥, ∨(parseformula("p"), parseformula("q")), FiniteHeytingAlgebra(H4)) == true
@test alphasat(α, ∨(parseformula("p"), parseformula("q")), FiniteHeytingAlgebra(H4)) == true
@test alphasat(β, ∨(parseformula("p"), parseformula("q")), FiniteHeytingAlgebra(H4)) == true
@test alphasat(⊤, ∨(parseformula("p"), parseformula("q")), FiniteHeytingAlgebra(H4)) == true

@test alphasat(⊥, ∨(parseformula("q"), parseformula("q")), FiniteHeytingAlgebra(H4)) == true
@test alphasat(α, ∨(parseformula("q"), parseformula("q")), FiniteHeytingAlgebra(H4)) == true
@test alphasat(β, ∨(parseformula("q"), parseformula("q")), FiniteHeytingAlgebra(H4)) == true
@test alphasat(⊤, ∨(parseformula("q"), parseformula("q")), FiniteHeytingAlgebra(H4)) == true

############################################################################################
## (Strong) conjunction ####################################################################
############################################################################################

@test alphasat(⊥, ∧(⊥, ⊥), FiniteHeytingAlgebra(H4)) == true
@test alphasat(⊥, ∧(⊥, α), FiniteHeytingAlgebra(H4)) == true
@test alphasat(⊥, ∧(⊥, β), FiniteHeytingAlgebra(H4)) == true
@test alphasat(⊥, ∧(⊥, ⊤), FiniteHeytingAlgebra(H4)) == true
@test alphasat(⊥, ∧(α, ⊥), FiniteHeytingAlgebra(H4)) == true
@test alphasat(⊥, ∧(α, α), FiniteHeytingAlgebra(H4)) == true
@test alphasat(⊥, ∧(α, β), FiniteHeytingAlgebra(H4)) == true
@test alphasat(⊥, ∧(α, ⊤), FiniteHeytingAlgebra(H4)) == true
@test alphasat(⊥, ∧(β, ⊥), FiniteHeytingAlgebra(H4)) == true
@test alphasat(⊥, ∧(β, α), FiniteHeytingAlgebra(H4)) == true
@test alphasat(⊥, ∧(β, β), FiniteHeytingAlgebra(H4)) == true
@test alphasat(⊥, ∧(β, ⊤), FiniteHeytingAlgebra(H4)) == true
@test alphasat(⊥, ∧(⊤, ⊥), FiniteHeytingAlgebra(H4)) == true
@test alphasat(⊥, ∧(⊤, α), FiniteHeytingAlgebra(H4)) == true
@test alphasat(⊥, ∧(⊤, β), FiniteHeytingAlgebra(H4)) == true
@test alphasat(⊥, ∧(⊤, ⊤), FiniteHeytingAlgebra(H4)) == true

@test alphasat(α, ∧(⊥, ⊥), FiniteHeytingAlgebra(H4)) == false
@test alphasat(α, ∧(⊥, α), FiniteHeytingAlgebra(H4)) == false
@test alphasat(α, ∧(⊥, β), FiniteHeytingAlgebra(H4)) == false
@test alphasat(α, ∧(⊥, ⊤), FiniteHeytingAlgebra(H4)) == false
@test alphasat(α, ∧(α, ⊥), FiniteHeytingAlgebra(H4)) == false
@test alphasat(α, ∧(α, α), FiniteHeytingAlgebra(H4)) == true
@test alphasat(α, ∧(α, β), FiniteHeytingAlgebra(H4)) == false
@test alphasat(α, ∧(α, ⊤), FiniteHeytingAlgebra(H4)) == true
@test alphasat(α, ∧(β, ⊥), FiniteHeytingAlgebra(H4)) == false
@test alphasat(α, ∧(β, α), FiniteHeytingAlgebra(H4)) == false
@test alphasat(α, ∧(β, β), FiniteHeytingAlgebra(H4)) == false
@test alphasat(α, ∧(β, ⊤), FiniteHeytingAlgebra(H4)) == false
@test alphasat(α, ∧(⊤, ⊥), FiniteHeytingAlgebra(H4)) == false
@test alphasat(α, ∧(⊤, α), FiniteHeytingAlgebra(H4)) == true
@test alphasat(α, ∧(⊤, β), FiniteHeytingAlgebra(H4)) == false
@test alphasat(α, ∧(⊤, ⊤), FiniteHeytingAlgebra(H4)) == true

@test alphasat(β, ∧(⊥, ⊥), FiniteHeytingAlgebra(H4)) == false
@test alphasat(β, ∧(⊥, α), FiniteHeytingAlgebra(H4)) == false
@test alphasat(β, ∧(⊥, β), FiniteHeytingAlgebra(H4)) == false
@test alphasat(β, ∧(⊥, ⊤), FiniteHeytingAlgebra(H4)) == false
@test alphasat(β, ∧(α, ⊥), FiniteHeytingAlgebra(H4)) == false
@test alphasat(β, ∧(α, α), FiniteHeytingAlgebra(H4)) == false
@test alphasat(β, ∧(α, β), FiniteHeytingAlgebra(H4)) == false
@test alphasat(β, ∧(α, ⊤), FiniteHeytingAlgebra(H4)) == false
@test alphasat(β, ∧(β, ⊥), FiniteHeytingAlgebra(H4)) == false
@test alphasat(β, ∧(β, α), FiniteHeytingAlgebra(H4)) == false
@test alphasat(β, ∧(β, β), FiniteHeytingAlgebra(H4)) == true
@test alphasat(β, ∧(β, ⊤), FiniteHeytingAlgebra(H4)) == true
@test alphasat(β, ∧(⊤, ⊥), FiniteHeytingAlgebra(H4)) == false
@test alphasat(β, ∧(⊤, α), FiniteHeytingAlgebra(H4)) == false
@test alphasat(β, ∧(⊤, β), FiniteHeytingAlgebra(H4)) == true
@test alphasat(β, ∧(⊤, ⊤), FiniteHeytingAlgebra(H4)) == true

@test alphasat(⊤, ∧(⊥, ⊥), FiniteHeytingAlgebra(H4)) == false
@test alphasat(⊤, ∧(⊥, α), FiniteHeytingAlgebra(H4)) == false
@test alphasat(⊤, ∧(⊥, β), FiniteHeytingAlgebra(H4)) == false
@test alphasat(⊤, ∧(⊥, ⊤), FiniteHeytingAlgebra(H4)) == false
@test alphasat(⊤, ∧(α, ⊥), FiniteHeytingAlgebra(H4)) == false
@test alphasat(⊤, ∧(α, α), FiniteHeytingAlgebra(H4)) == false
@test alphasat(⊤, ∧(α, β), FiniteHeytingAlgebra(H4)) == false
@test alphasat(⊤, ∧(α, ⊤), FiniteHeytingAlgebra(H4)) == false
@test alphasat(⊤, ∧(β, ⊥), FiniteHeytingAlgebra(H4)) == false
@test alphasat(⊤, ∧(β, α), FiniteHeytingAlgebra(H4)) == false
@test alphasat(⊤, ∧(β, β), FiniteHeytingAlgebra(H4)) == false
@test alphasat(⊤, ∧(β, ⊤), FiniteHeytingAlgebra(H4)) == false
@test alphasat(⊤, ∧(⊤, ⊥), FiniteHeytingAlgebra(H4)) == false
@test alphasat(⊤, ∧(⊤, α), FiniteHeytingAlgebra(H4)) == false
@test alphasat(⊤, ∧(⊤, β), FiniteHeytingAlgebra(H4)) == false
@test alphasat(⊤, ∧(⊤, ⊤), FiniteHeytingAlgebra(H4)) == true

@test alphasat(⊥, ∧(parseformula("p"), ⊥), FiniteHeytingAlgebra(H4)) == true
@test alphasat(⊥, ∧(parseformula("p"), α), FiniteHeytingAlgebra(H4)) == true
@test alphasat(⊥, ∧(parseformula("p"), β), FiniteHeytingAlgebra(H4)) == true
@test alphasat(⊥, ∧(parseformula("p"), ⊤), FiniteHeytingAlgebra(H4)) == true
@test alphasat(α, ∧(parseformula("p"), ⊥), FiniteHeytingAlgebra(H4)) == false
@test alphasat(α, ∧(parseformula("p"), α), FiniteHeytingAlgebra(H4)) == true
@test alphasat(α, ∧(parseformula("p"), β), FiniteHeytingAlgebra(H4)) == false
@test alphasat(α, ∧(parseformula("p"), ⊤), FiniteHeytingAlgebra(H4)) == true
@test alphasat(β, ∧(parseformula("p"), ⊥), FiniteHeytingAlgebra(H4)) == false
@test alphasat(β, ∧(parseformula("p"), α), FiniteHeytingAlgebra(H4)) == false
@test alphasat(β, ∧(parseformula("p"), β), FiniteHeytingAlgebra(H4)) == true
@test alphasat(β, ∧(parseformula("p"), ⊤), FiniteHeytingAlgebra(H4)) == true
@test alphasat(⊤, ∧(parseformula("p"), ⊥), FiniteHeytingAlgebra(H4)) == false
@test alphasat(⊤, ∧(parseformula("p"), α), FiniteHeytingAlgebra(H4)) == false
@test alphasat(⊤, ∧(parseformula("p"), β), FiniteHeytingAlgebra(H4)) == false
@test alphasat(⊤, ∧(parseformula("p"), ⊤), FiniteHeytingAlgebra(H4)) == true

@test alphasat(⊥, ∧(⊥, parseformula("p")), FiniteHeytingAlgebra(H4)) == true
@test alphasat(⊥, ∧(α, parseformula("p")), FiniteHeytingAlgebra(H4)) == true
@test alphasat(⊥, ∧(β, parseformula("p")), FiniteHeytingAlgebra(H4)) == true
@test alphasat(⊥, ∧(⊤, parseformula("p")), FiniteHeytingAlgebra(H4)) == true
@test alphasat(α, ∧(⊥, parseformula("p")), FiniteHeytingAlgebra(H4)) == false
@test alphasat(α, ∧(α, parseformula("p")), FiniteHeytingAlgebra(H4)) == true
@test alphasat(α, ∧(β, parseformula("p")), FiniteHeytingAlgebra(H4)) == false
@test alphasat(α, ∧(⊤, parseformula("p")), FiniteHeytingAlgebra(H4)) == true
@test alphasat(β, ∧(⊥, parseformula("p")), FiniteHeytingAlgebra(H4)) == false
@test alphasat(β, ∧(α, parseformula("p")), FiniteHeytingAlgebra(H4)) == false
@test alphasat(β, ∧(β, parseformula("p")), FiniteHeytingAlgebra(H4)) == true
@test alphasat(β, ∧(⊤, parseformula("p")), FiniteHeytingAlgebra(H4)) == true
@test alphasat(⊤, ∧(⊥, parseformula("p")), FiniteHeytingAlgebra(H4)) == false
@test alphasat(⊤, ∧(α, parseformula("p")), FiniteHeytingAlgebra(H4)) == false
@test alphasat(⊤, ∧(β, parseformula("p")), FiniteHeytingAlgebra(H4)) == false
@test alphasat(⊤, ∧(⊤, parseformula("p")), FiniteHeytingAlgebra(H4)) == true

@test alphasat(⊥, ∧(parseformula("p"), parseformula("p")), FiniteHeytingAlgebra(H4)) == true
@test alphasat(α, ∧(parseformula("p"), parseformula("p")), FiniteHeytingAlgebra(H4)) == true
@test alphasat(β, ∧(parseformula("p"), parseformula("p")), FiniteHeytingAlgebra(H4)) == true
@test alphasat(⊤, ∧(parseformula("p"), parseformula("p")), FiniteHeytingAlgebra(H4)) == true

@test alphasat(⊥, ∧(parseformula("p"), parseformula("q")), FiniteHeytingAlgebra(H4)) == true
@test alphasat(α, ∧(parseformula("p"), parseformula("q")), FiniteHeytingAlgebra(H4)) == true
@test alphasat(β, ∧(parseformula("p"), parseformula("q")), FiniteHeytingAlgebra(H4)) == true
@test alphasat(⊤, ∧(parseformula("p"), parseformula("q")), FiniteHeytingAlgebra(H4)) == true

@test alphasat(⊥, ∧(parseformula("q"), parseformula("p")), FiniteHeytingAlgebra(H4)) == true
@test alphasat(α, ∧(parseformula("q"), parseformula("p")), FiniteHeytingAlgebra(H4)) == true
@test alphasat(β, ∧(parseformula("q"), parseformula("p")), FiniteHeytingAlgebra(H4)) == true
@test alphasat(⊤, ∧(parseformula("q"), parseformula("p")), FiniteHeytingAlgebra(H4)) == true

############################################################################################
## Implication #############################################################################
############################################################################################

@test alphasat(⊥, →(⊥, ⊥), FiniteHeytingAlgebra(H4)) == true
@test alphasat(⊥, →(⊥, α), FiniteHeytingAlgebra(H4)) == true
@test alphasat(⊥, →(⊥, β), FiniteHeytingAlgebra(H4)) == true
@test alphasat(⊥, →(⊥, ⊤), FiniteHeytingAlgebra(H4)) == true
@test alphasat(⊥, →(α, ⊥), FiniteHeytingAlgebra(H4)) == true
@test alphasat(⊥, →(α, α), FiniteHeytingAlgebra(H4)) == true
@test alphasat(⊥, →(α, β), FiniteHeytingAlgebra(H4)) == true
@test alphasat(⊥, →(α, ⊤), FiniteHeytingAlgebra(H4)) == true
@test alphasat(⊥, →(β, ⊥), FiniteHeytingAlgebra(H4)) == true
@test alphasat(⊥, →(β, α), FiniteHeytingAlgebra(H4)) == true
@test alphasat(⊥, →(β, β), FiniteHeytingAlgebra(H4)) == true
@test alphasat(⊥, →(β, ⊤), FiniteHeytingAlgebra(H4)) == true
@test alphasat(⊥, →(⊤, ⊥), FiniteHeytingAlgebra(H4)) == true
@test alphasat(⊥, →(⊤, α), FiniteHeytingAlgebra(H4)) == true
@test alphasat(⊥, →(⊤, β), FiniteHeytingAlgebra(H4)) == true
@test alphasat(⊥, →(⊤, ⊤), FiniteHeytingAlgebra(H4)) == true

@test alphasat(α, →(⊥, ⊥), FiniteHeytingAlgebra(H4)) == true
@test alphasat(α, →(⊥, α), FiniteHeytingAlgebra(H4)) == true
@test alphasat(α, →(⊥, β), FiniteHeytingAlgebra(H4)) == true
@test alphasat(α, →(⊥, ⊤), FiniteHeytingAlgebra(H4)) == true
@test alphasat(α, →(α, ⊥), FiniteHeytingAlgebra(H4)) == false
@test alphasat(α, →(α, α), FiniteHeytingAlgebra(H4)) == true
@test alphasat(α, →(α, β), FiniteHeytingAlgebra(H4)) == false
@test alphasat(α, →(α, ⊤), FiniteHeytingAlgebra(H4)) == true
@test alphasat(α, →(β, ⊥), FiniteHeytingAlgebra(H4)) == true
@test alphasat(α, →(β, α), FiniteHeytingAlgebra(H4)) == true
@test alphasat(α, →(β, β), FiniteHeytingAlgebra(H4)) == true
@test alphasat(α, →(β, ⊤), FiniteHeytingAlgebra(H4)) == true
@test alphasat(α, →(⊤, ⊥), FiniteHeytingAlgebra(H4)) == false
@test alphasat(α, →(⊤, α), FiniteHeytingAlgebra(H4)) == true
@test alphasat(α, →(⊤, β), FiniteHeytingAlgebra(H4)) == false
@test alphasat(α, →(⊤, ⊤), FiniteHeytingAlgebra(H4)) == true

@test alphasat(β, →(⊥, ⊥), FiniteHeytingAlgebra(H4)) == true
@test alphasat(β, →(⊥, α), FiniteHeytingAlgebra(H4)) == true
@test alphasat(β, →(⊥, β), FiniteHeytingAlgebra(H4)) == true
@test alphasat(β, →(⊥, ⊤), FiniteHeytingAlgebra(H4)) == true
@test alphasat(β, →(α, ⊥), FiniteHeytingAlgebra(H4)) == true
@test alphasat(β, →(α, α), FiniteHeytingAlgebra(H4)) == true
@test alphasat(β, →(α, β), FiniteHeytingAlgebra(H4)) == true
@test alphasat(β, →(α, ⊤), FiniteHeytingAlgebra(H4)) == true
@test alphasat(β, →(β, ⊥), FiniteHeytingAlgebra(H4)) == false
@test alphasat(β, →(β, α), FiniteHeytingAlgebra(H4)) == false
@test alphasat(β, →(β, β), FiniteHeytingAlgebra(H4)) == true
@test alphasat(β, →(β, ⊤), FiniteHeytingAlgebra(H4)) == true
@test alphasat(β, →(⊤, ⊥), FiniteHeytingAlgebra(H4)) == false
@test alphasat(β, →(⊤, α), FiniteHeytingAlgebra(H4)) == false
@test alphasat(β, →(⊤, β), FiniteHeytingAlgebra(H4)) == true
@test alphasat(β, →(⊤, ⊤), FiniteHeytingAlgebra(H4)) == true

@test alphasat(⊤, →(⊥, ⊥), FiniteHeytingAlgebra(H4)) == true
@test alphasat(⊤, →(⊥, α), FiniteHeytingAlgebra(H4)) == true
@test alphasat(⊤, →(⊥, β), FiniteHeytingAlgebra(H4)) == true
@test alphasat(⊤, →(⊥, ⊤), FiniteHeytingAlgebra(H4)) == true
@test alphasat(⊤, →(α, ⊥), FiniteHeytingAlgebra(H4)) == false
@test alphasat(⊤, →(α, α), FiniteHeytingAlgebra(H4)) == true
@test alphasat(⊤, →(α, β), FiniteHeytingAlgebra(H4)) == false
@test alphasat(⊤, →(α, ⊤), FiniteHeytingAlgebra(H4)) == true
@test alphasat(⊤, →(β, ⊥), FiniteHeytingAlgebra(H4)) == false
@test alphasat(⊤, →(β, α), FiniteHeytingAlgebra(H4)) == false
@test alphasat(⊤, →(β, β), FiniteHeytingAlgebra(H4)) == true
@test alphasat(⊤, →(β, ⊤), FiniteHeytingAlgebra(H4)) == true
@test alphasat(⊤, →(⊤, ⊥), FiniteHeytingAlgebra(H4)) == false
@test alphasat(⊤, →(⊤, α), FiniteHeytingAlgebra(H4)) == false
@test alphasat(⊤, →(⊤, β), FiniteHeytingAlgebra(H4)) == false
@test alphasat(⊤, →(⊤, ⊤), FiniteHeytingAlgebra(H4)) == true

@test alphasat(⊥, →(parseformula("p"), ⊥), FiniteHeytingAlgebra(H4)) == true
@test alphasat(⊥, →(parseformula("p"), α), FiniteHeytingAlgebra(H4)) == true
@test alphasat(⊥, →(parseformula("p"), β), FiniteHeytingAlgebra(H4)) == true
@test alphasat(⊥, →(parseformula("p"), ⊤), FiniteHeytingAlgebra(H4)) == true
@test alphasat(α, →(parseformula("p"), ⊥), FiniteHeytingAlgebra(H4)) == true
@test alphasat(α, →(parseformula("p"), α), FiniteHeytingAlgebra(H4)) == true
@test alphasat(α, →(parseformula("p"), β), FiniteHeytingAlgebra(H4)) == true
@test alphasat(α, →(parseformula("p"), ⊤), FiniteHeytingAlgebra(H4)) == true
@test alphasat(β, →(parseformula("p"), ⊥), FiniteHeytingAlgebra(H4)) == true
@test alphasat(β, →(parseformula("p"), α), FiniteHeytingAlgebra(H4)) == true
@test alphasat(β, →(parseformula("p"), β), FiniteHeytingAlgebra(H4)) == true
@test alphasat(β, →(parseformula("p"), ⊤), FiniteHeytingAlgebra(H4)) == true
@test alphasat(⊤, →(parseformula("p"), ⊥), FiniteHeytingAlgebra(H4)) == true
@test alphasat(⊤, →(parseformula("p"), α), FiniteHeytingAlgebra(H4)) == true
@test alphasat(⊤, →(parseformula("p"), β), FiniteHeytingAlgebra(H4)) == true
@test alphasat(⊤, →(parseformula("p"), ⊤), FiniteHeytingAlgebra(H4)) == true

@test alphasat(⊥, →(⊥, parseformula("p")), FiniteHeytingAlgebra(H4)) == true
@test alphasat(⊥, →(α, parseformula("p")), FiniteHeytingAlgebra(H4)) == true
@test alphasat(⊥, →(β, parseformula("p")), FiniteHeytingAlgebra(H4)) == true
@test alphasat(⊥, →(⊤, parseformula("p")), FiniteHeytingAlgebra(H4)) == true
@test alphasat(α, →(⊥, parseformula("p")), FiniteHeytingAlgebra(H4)) == true
@test alphasat(α, →(α, parseformula("p")), FiniteHeytingAlgebra(H4)) == true
@test alphasat(α, →(β, parseformula("p")), FiniteHeytingAlgebra(H4)) == true
@test alphasat(α, →(⊤, parseformula("p")), FiniteHeytingAlgebra(H4)) == true
@test alphasat(β, →(⊥, parseformula("p")), FiniteHeytingAlgebra(H4)) == true
@test alphasat(β, →(α, parseformula("p")), FiniteHeytingAlgebra(H4)) == true
@test alphasat(β, →(β, parseformula("p")), FiniteHeytingAlgebra(H4)) == true
@test alphasat(β, →(⊤, parseformula("p")), FiniteHeytingAlgebra(H4)) == true
@test alphasat(⊤, →(⊥, parseformula("p")), FiniteHeytingAlgebra(H4)) == true
@test alphasat(⊤, →(α, parseformula("p")), FiniteHeytingAlgebra(H4)) == true
@test alphasat(⊤, →(β, parseformula("p")), FiniteHeytingAlgebra(H4)) == true
@test alphasat(⊤, →(⊤, parseformula("p")), FiniteHeytingAlgebra(H4)) == true

@test alphasat(⊥, →(parseformula("p"), parseformula("p")), FiniteHeytingAlgebra(H4)) == true
@test alphasat(α, →(parseformula("p"), parseformula("p")), FiniteHeytingAlgebra(H4)) == true
@test alphasat(β, →(parseformula("p"), parseformula("p")), FiniteHeytingAlgebra(H4)) == true
@test alphasat(⊤, →(parseformula("p"), parseformula("p")), FiniteHeytingAlgebra(H4)) == true

@test alphasat(⊥, →(parseformula("p"), parseformula("q")), FiniteHeytingAlgebra(H4)) == true
@test alphasat(α, →(parseformula("p"), parseformula("q")), FiniteHeytingAlgebra(H4)) == true
@test alphasat(β, →(parseformula("p"), parseformula("q")), FiniteHeytingAlgebra(H4)) == true
@test alphasat(⊤, →(parseformula("p"), parseformula("q")), FiniteHeytingAlgebra(H4)) == true

@test alphasat(⊥, →(parseformula("q"), parseformula("p")), FiniteHeytingAlgebra(H4)) == true
@test alphasat(α, →(parseformula("q"), parseformula("p")), FiniteHeytingAlgebra(H4)) == true
@test alphasat(β, →(parseformula("q"), parseformula("p")), FiniteHeytingAlgebra(H4)) == true
@test alphasat(⊤, →(parseformula("q"), parseformula("p")), FiniteHeytingAlgebra(H4)) == true

############################################################################################
#### H9 ####################################################################################
############################################################################################

include("algebras/h9.jl")

BASE_MANY_VALUED_CONNECTIVES = [∨, ∧, →]
BaseManyValuedConnectives = Union{typeof.(BASE_MANY_VALUED_CONNECTIVES)...}

############################################################################################
#### Old and new rules compatibility #######################################################
############################################################################################

for i ∈ d9
    for j ∈ d9
        @test alphasat(
            i,
            j,
            FiniteHeytingAlgebra(H9)
        ) == alphasat(
            i,
            j,
            FiniteHeytingAlgebra(H9),
            oldrule=true
        )
        for k ∈ d9
            for o ∈ BASE_MANY_VALUED_CONNECTIVES
                @test alphasat(
                    k,
                    o(i, j),
                    FiniteHeytingAlgebra(H9)
                ) == alphasat(
                    k,
                    o(i, j),
                    FiniteHeytingAlgebra(H9),
                    oldrule=true
                ) 
            end
        end
    end
end
