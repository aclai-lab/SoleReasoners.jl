############################################################################################
#### H4 ####################################################################################
############################################################################################

include("algebras/h4.jl")

############################################################################################
## Base cases ##############################################################################
############################################################################################

for i ∈ getdomain(FiniteHeytingAlgebra(H4))
    for j ∈ getdomain(FiniteHeytingAlgebra(H4))
        @test alphasat(i, j, FiniteHeytingAlgebra(H4)) == alphaprove(i, j, FiniteHeytingAlgebra(H4))
        for k ∈ getdomain(FiniteHeytingAlgebra(H4))
            @test alphasat(i, ∨(j,k), FiniteHeytingAlgebra(H4)) == alphaprove(i, ∨(j,k), FiniteHeytingAlgebra(H4))
            @test alphasat(i, ∧(j,k), FiniteHeytingAlgebra(H4)) == alphaprove(i, ∧(j,k), FiniteHeytingAlgebra(H4))
            @test alphasat(i, →(j,k), FiniteHeytingAlgebra(H4)) == alphaprove(i, →(j,k), FiniteHeytingAlgebra(H4))
        end
    end
end

@test alphaprove(⊥, parseformula("p"), FiniteHeytingAlgebra(H4)) == true
@test alphaprove(α, parseformula("p"), FiniteHeytingAlgebra(H4)) == false
@test alphaprove(β, parseformula("p"), FiniteHeytingAlgebra(H4)) == false
@test alphaprove(⊤, parseformula("p"), FiniteHeytingAlgebra(H4)) == false

############################################################################################
## (Strong) disjuction #####################################################################
############################################################################################

@test alphaprove(⊥, ∨(parseformula("p"), ⊥), FiniteHeytingAlgebra(H4)) == true
@test alphaprove(⊥, ∨(parseformula("p"), α), FiniteHeytingAlgebra(H4)) == true
@test alphaprove(⊥, ∨(parseformula("p"), β), FiniteHeytingAlgebra(H4)) == true
@test alphaprove(⊥, ∨(parseformula("p"), ⊤), FiniteHeytingAlgebra(H4)) == true
@test alphaprove(α, ∨(parseformula("p"), ⊥), FiniteHeytingAlgebra(H4)) == false
@test alphaprove(α, ∨(parseformula("p"), α), FiniteHeytingAlgebra(H4)) == true
@test alphaprove(α, ∨(parseformula("p"), β), FiniteHeytingAlgebra(H4)) == false
@test alphaprove(α, ∨(parseformula("p"), ⊤), FiniteHeytingAlgebra(H4)) == true
@test alphaprove(β, ∨(parseformula("p"), ⊥), FiniteHeytingAlgebra(H4)) == false
@test alphaprove(β, ∨(parseformula("p"), α), FiniteHeytingAlgebra(H4)) == false
@test alphaprove(β, ∨(parseformula("p"), β), FiniteHeytingAlgebra(H4)) == true
@test alphaprove(β, ∨(parseformula("p"), ⊤), FiniteHeytingAlgebra(H4)) == true
@test alphaprove(⊤, ∨(parseformula("p"), ⊥), FiniteHeytingAlgebra(H4)) == false
@test alphaprove(⊤, ∨(parseformula("p"), α), FiniteHeytingAlgebra(H4)) == false
@test alphaprove(⊤, ∨(parseformula("p"), β), FiniteHeytingAlgebra(H4)) == false
@test alphaprove(⊤, ∨(parseformula("p"), ⊤), FiniteHeytingAlgebra(H4)) == true

@test alphaprove(⊥, ∨(⊥, parseformula("p")), FiniteHeytingAlgebra(H4)) == true 
@test alphaprove(⊥, ∨(α, parseformula("p")), FiniteHeytingAlgebra(H4)) == true 
@test alphaprove(⊥, ∨(β, parseformula("p")), FiniteHeytingAlgebra(H4)) == true 
@test alphaprove(⊥, ∨(⊤, parseformula("p")), FiniteHeytingAlgebra(H4)) == true 
@test alphaprove(α, ∨(⊥, parseformula("p")), FiniteHeytingAlgebra(H4)) == false
@test alphaprove(α, ∨(α, parseformula("p")), FiniteHeytingAlgebra(H4)) == true 
@test alphaprove(α, ∨(β, parseformula("p")), FiniteHeytingAlgebra(H4)) == false 
@test alphaprove(α, ∨(⊤, parseformula("p")), FiniteHeytingAlgebra(H4)) == true 
@test alphaprove(β, ∨(⊥, parseformula("p")), FiniteHeytingAlgebra(H4)) == false 
@test alphaprove(β, ∨(α, parseformula("p")), FiniteHeytingAlgebra(H4)) == false 
@test alphaprove(β, ∨(β, parseformula("p")), FiniteHeytingAlgebra(H4)) == true 
@test alphaprove(β, ∨(⊤, parseformula("p")), FiniteHeytingAlgebra(H4)) == true 
@test alphaprove(⊤, ∨(⊥, parseformula("p")), FiniteHeytingAlgebra(H4)) == false 
@test alphaprove(⊤, ∨(α, parseformula("p")), FiniteHeytingAlgebra(H4)) == false 
@test alphaprove(⊤, ∨(β, parseformula("p")), FiniteHeytingAlgebra(H4)) == false 
@test alphaprove(⊤, ∨(⊤, parseformula("p")), FiniteHeytingAlgebra(H4)) == true 

@test alphaprove(⊥, ∨(parseformula("p"), parseformula("p")), FiniteHeytingAlgebra(H4)) == true
@test alphaprove(α, ∨(parseformula("p"), parseformula("p")), FiniteHeytingAlgebra(H4)) == false
@test alphaprove(β, ∨(parseformula("p"), parseformula("p")), FiniteHeytingAlgebra(H4)) == false
@test alphaprove(⊤, ∨(parseformula("p"), parseformula("p")), FiniteHeytingAlgebra(H4)) == false

@test alphaprove(⊥, ∨(parseformula("p"), parseformula("q")), FiniteHeytingAlgebra(H4)) == true
@test alphaprove(α, ∨(parseformula("p"), parseformula("q")), FiniteHeytingAlgebra(H4)) == false
@test alphaprove(β, ∨(parseformula("p"), parseformula("q")), FiniteHeytingAlgebra(H4)) == false
@test alphaprove(⊤, ∨(parseformula("p"), parseformula("q")), FiniteHeytingAlgebra(H4)) == false

@test alphaprove(⊥, ∨(parseformula("q"), parseformula("p")), FiniteHeytingAlgebra(H4)) == true
@test alphaprove(α, ∨(parseformula("q"), parseformula("p")), FiniteHeytingAlgebra(H4)) == false
@test alphaprove(β, ∨(parseformula("q"), parseformula("p")), FiniteHeytingAlgebra(H4)) == false
@test alphaprove(⊤, ∨(parseformula("q"), parseformula("p")), FiniteHeytingAlgebra(H4)) == false

############################################################################################
## (Strong) conjunction ####################################################################
############################################################################################

@test alphaprove(⊥, ∧(parseformula("p"), ⊥), FiniteHeytingAlgebra(H4)) == true
@test alphaprove(⊥, ∧(parseformula("p"), α), FiniteHeytingAlgebra(H4)) == true
@test alphaprove(⊥, ∧(parseformula("p"), β), FiniteHeytingAlgebra(H4)) == true
@test alphaprove(⊥, ∧(parseformula("p"), ⊤), FiniteHeytingAlgebra(H4)) == true
@test alphaprove(α, ∧(parseformula("p"), ⊥), FiniteHeytingAlgebra(H4)) == false
@test alphaprove(α, ∧(parseformula("p"), α), FiniteHeytingAlgebra(H4)) == false
@test alphaprove(α, ∧(parseformula("p"), β), FiniteHeytingAlgebra(H4)) == false
@test alphaprove(α, ∧(parseformula("p"), ⊤), FiniteHeytingAlgebra(H4)) == false
@test alphaprove(β, ∧(parseformula("p"), ⊥), FiniteHeytingAlgebra(H4)) == false
@test alphaprove(β, ∧(parseformula("p"), α), FiniteHeytingAlgebra(H4)) == false
@test alphaprove(β, ∧(parseformula("p"), β), FiniteHeytingAlgebra(H4)) == false
@test alphaprove(β, ∧(parseformula("p"), ⊤), FiniteHeytingAlgebra(H4)) == false
@test alphaprove(⊤, ∧(parseformula("p"), ⊥), FiniteHeytingAlgebra(H4)) == false
@test alphaprove(⊤, ∧(parseformula("p"), α), FiniteHeytingAlgebra(H4)) == false
@test alphaprove(⊤, ∧(parseformula("p"), β), FiniteHeytingAlgebra(H4)) == false
@test alphaprove(⊤, ∧(parseformula("p"), ⊤), FiniteHeytingAlgebra(H4)) == false

@test alphaprove(⊥, ∧(⊥, parseformula("p")), FiniteHeytingAlgebra(H4)) == true 
@test alphaprove(⊥, ∧(α, parseformula("p")), FiniteHeytingAlgebra(H4)) == true 
@test alphaprove(⊥, ∧(β, parseformula("p")), FiniteHeytingAlgebra(H4)) == true 
@test alphaprove(⊥, ∧(⊤, parseformula("p")), FiniteHeytingAlgebra(H4)) == true 
@test alphaprove(α, ∧(⊥, parseformula("p")), FiniteHeytingAlgebra(H4)) == false
@test alphaprove(α, ∧(α, parseformula("p")), FiniteHeytingAlgebra(H4)) == false 
@test alphaprove(α, ∧(β, parseformula("p")), FiniteHeytingAlgebra(H4)) == false 
@test alphaprove(α, ∧(⊤, parseformula("p")), FiniteHeytingAlgebra(H4)) == false 
@test alphaprove(β, ∧(⊥, parseformula("p")), FiniteHeytingAlgebra(H4)) == false 
@test alphaprove(β, ∧(α, parseformula("p")), FiniteHeytingAlgebra(H4)) == false 
@test alphaprove(β, ∧(β, parseformula("p")), FiniteHeytingAlgebra(H4)) == false 
@test alphaprove(β, ∧(⊤, parseformula("p")), FiniteHeytingAlgebra(H4)) == false 
@test alphaprove(⊤, ∧(⊥, parseformula("p")), FiniteHeytingAlgebra(H4)) == false 
@test alphaprove(⊤, ∧(α, parseformula("p")), FiniteHeytingAlgebra(H4)) == false 
@test alphaprove(⊤, ∧(β, parseformula("p")), FiniteHeytingAlgebra(H4)) == false 
@test alphaprove(⊤, ∧(⊤, parseformula("p")), FiniteHeytingAlgebra(H4)) == false 

@test alphaprove(⊥, ∧(parseformula("p"), parseformula("p")), FiniteHeytingAlgebra(H4)) == true
@test alphaprove(α, ∧(parseformula("p"), parseformula("p")), FiniteHeytingAlgebra(H4)) == false
@test alphaprove(β, ∧(parseformula("p"), parseformula("p")), FiniteHeytingAlgebra(H4)) == false
@test alphaprove(⊤, ∧(parseformula("p"), parseformula("p")), FiniteHeytingAlgebra(H4)) == false

@test alphaprove(⊥, ∧(parseformula("p"), parseformula("q")), FiniteHeytingAlgebra(H4)) == true
@test alphaprove(α, ∧(parseformula("p"), parseformula("q")), FiniteHeytingAlgebra(H4)) == false
@test alphaprove(β, ∧(parseformula("p"), parseformula("q")), FiniteHeytingAlgebra(H4)) == false
@test alphaprove(⊤, ∧(parseformula("p"), parseformula("q")), FiniteHeytingAlgebra(H4)) == false

@test alphaprove(⊥, ∧(parseformula("q"), parseformula("p")), FiniteHeytingAlgebra(H4)) == true
@test alphaprove(α, ∧(parseformula("q"), parseformula("p")), FiniteHeytingAlgebra(H4)) == false
@test alphaprove(β, ∧(parseformula("q"), parseformula("p")), FiniteHeytingAlgebra(H4)) == false
@test alphaprove(⊤, ∧(parseformula("q"), parseformula("p")), FiniteHeytingAlgebra(H4)) == false

############################################################################################
## Implication #############################################################################
############################################################################################

@test alphaprove(⊥, →(parseformula("p"), ⊥), FiniteHeytingAlgebra(H4)) == true
@test alphaprove(⊥, →(parseformula("p"), α), FiniteHeytingAlgebra(H4)) == true
@test alphaprove(⊥, →(parseformula("p"), β), FiniteHeytingAlgebra(H4)) == true
@test alphaprove(⊥, →(parseformula("p"), ⊤), FiniteHeytingAlgebra(H4)) == true
@test alphaprove(α, →(parseformula("p"), ⊥), FiniteHeytingAlgebra(H4)) == false
@test alphaprove(α, →(parseformula("p"), α), FiniteHeytingAlgebra(H4)) == true
@test alphaprove(α, →(parseformula("p"), β), FiniteHeytingAlgebra(H4)) == false
@test alphaprove(α, →(parseformula("p"), ⊤), FiniteHeytingAlgebra(H4)) == true
@test alphaprove(β, →(parseformula("p"), ⊥), FiniteHeytingAlgebra(H4)) == false
@test alphaprove(β, →(parseformula("p"), α), FiniteHeytingAlgebra(H4)) == false
@test alphaprove(β, →(parseformula("p"), β), FiniteHeytingAlgebra(H4)) == true
@test alphaprove(β, →(parseformula("p"), ⊤), FiniteHeytingAlgebra(H4)) == true
@test alphaprove(⊤, →(parseformula("p"), ⊥), FiniteHeytingAlgebra(H4)) == false
@test alphaprove(⊤, →(parseformula("p"), α), FiniteHeytingAlgebra(H4)) == false
@test alphaprove(⊤, →(parseformula("p"), β), FiniteHeytingAlgebra(H4)) == false
@test alphaprove(⊤, →(parseformula("p"), ⊤), FiniteHeytingAlgebra(H4)) == true

@test alphaprove(⊥, →(⊥, parseformula("p")), FiniteHeytingAlgebra(H4)) == true
@test alphaprove(⊥, →(α, parseformula("p")), FiniteHeytingAlgebra(H4)) == true
@test alphaprove(⊥, →(β, parseformula("p")), FiniteHeytingAlgebra(H4)) == true
@test alphaprove(⊥, →(⊤, parseformula("p")), FiniteHeytingAlgebra(H4)) == true
@test alphaprove(α, →(⊥, parseformula("p")), FiniteHeytingAlgebra(H4)) == true
@test alphaprove(α, →(α, parseformula("p")), FiniteHeytingAlgebra(H4)) == false
@test alphaprove(α, →(β, parseformula("p")), FiniteHeytingAlgebra(H4)) == true
@test alphaprove(α, →(⊤, parseformula("p")), FiniteHeytingAlgebra(H4)) == false
@test alphaprove(β, →(⊥, parseformula("p")), FiniteHeytingAlgebra(H4)) == true
@test alphaprove(β, →(α, parseformula("p")), FiniteHeytingAlgebra(H4)) == true
@test alphaprove(β, →(β, parseformula("p")), FiniteHeytingAlgebra(H4)) == false
@test alphaprove(β, →(⊤, parseformula("p")), FiniteHeytingAlgebra(H4)) == false
@test alphaprove(⊤, →(⊥, parseformula("p")), FiniteHeytingAlgebra(H4)) == true
@test alphaprove(⊤, →(α, parseformula("p")), FiniteHeytingAlgebra(H4)) == false
@test alphaprove(⊤, →(β, parseformula("p")), FiniteHeytingAlgebra(H4)) == false
@test alphaprove(⊤, →(⊤, parseformula("p")), FiniteHeytingAlgebra(H4)) == false

@test alphaprove(⊥, →(parseformula("p"), parseformula("p")), FiniteHeytingAlgebra(H4)) == true
@test alphaprove(α, →(parseformula("p"), parseformula("p")), FiniteHeytingAlgebra(H4)) == true
@test alphaprove(β, →(parseformula("p"), parseformula("p")), FiniteHeytingAlgebra(H4)) == true
@test alphaprove(⊤, →(parseformula("p"), parseformula("p")), FiniteHeytingAlgebra(H4)) == true

@test alphaprove(⊥, →(parseformula("p"), parseformula("q")), FiniteHeytingAlgebra(H4)) == true
@test alphaprove(α, →(parseformula("p"), parseformula("q")), FiniteHeytingAlgebra(H4)) == false
@test alphaprove(β, →(parseformula("p"), parseformula("q")), FiniteHeytingAlgebra(H4)) == false
@test alphaprove(⊤, →(parseformula("p"), parseformula("q")), FiniteHeytingAlgebra(H4)) == false

@test alphaprove(⊥, →(parseformula("q"), parseformula("p")), FiniteHeytingAlgebra(H4)) == true
@test alphaprove(α, →(parseformula("q"), parseformula("p")), FiniteHeytingAlgebra(H4)) == false
@test alphaprove(β, →(parseformula("q"), parseformula("p")), FiniteHeytingAlgebra(H4)) == false
@test alphaprove(⊤, →(parseformula("q"), parseformula("p")), FiniteHeytingAlgebra(H4)) == false
