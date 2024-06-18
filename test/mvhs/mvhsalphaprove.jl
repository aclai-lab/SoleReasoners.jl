############################################################################################
#### H4 ####################################################################################
############################################################################################

using SoleLogics.ManyValuedLogics: H4
using SoleLogics.ManyValuedLogics: α, β

############################################################################################
## Base cases ##############################################################################
############################################################################################

for i ∈ getdomain(FiniteHeytingAlgebra(H4))
    for j ∈ getdomain(FiniteHeytingAlgebra(H4))
        @test mvhsalphasat(i, j, FiniteHeytingAlgebra(H4)) == mvhsalphaprove(i, j, FiniteHeytingAlgebra(H4))
        for k ∈ getdomain(FiniteHeytingAlgebra(H4))
            # println("$i\t$j\t$k")
            @test mvhsalphasat(i, ∨(j,k), FiniteHeytingAlgebra(H4)) == mvhsalphaprove(i, ∨(j,k), FiniteHeytingAlgebra(H4))
            @test mvhsalphasat(i, ∧(j,k), FiniteHeytingAlgebra(H4)) == mvhsalphaprove(i, ∧(j,k), FiniteHeytingAlgebra(H4))
            @test mvhsalphasat(i, →(j,k), FiniteHeytingAlgebra(H4)) == mvhsalphaprove(i, →(j,k), FiniteHeytingAlgebra(H4))
        end
    end
end

@test mvhsalphaprove(⊥, parseformula("p"), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphaprove(α, parseformula("p"), FiniteHeytingAlgebra(H4)) == false
@test mvhsalphaprove(β, parseformula("p"), FiniteHeytingAlgebra(H4)) == false
@test mvhsalphaprove(⊤, parseformula("p"), FiniteHeytingAlgebra(H4)) == false

############################################################################################
## (Strong) disjuction #####################################################################
############################################################################################

@test mvhsalphaprove(⊥, ∨(parseformula("p"), ⊥), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphaprove(⊥, ∨(parseformula("p"), α), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphaprove(⊥, ∨(parseformula("p"), β), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphaprove(⊥, ∨(parseformula("p"), ⊤), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphaprove(α, ∨(parseformula("p"), ⊥), FiniteHeytingAlgebra(H4)) == false
@test mvhsalphaprove(α, ∨(parseformula("p"), α), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphaprove(α, ∨(parseformula("p"), β), FiniteHeytingAlgebra(H4)) == false
@test mvhsalphaprove(α, ∨(parseformula("p"), ⊤), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphaprove(β, ∨(parseformula("p"), ⊥), FiniteHeytingAlgebra(H4)) == false
@test mvhsalphaprove(β, ∨(parseformula("p"), α), FiniteHeytingAlgebra(H4)) == false
@test mvhsalphaprove(β, ∨(parseformula("p"), β), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphaprove(β, ∨(parseformula("p"), ⊤), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphaprove(⊤, ∨(parseformula("p"), ⊥), FiniteHeytingAlgebra(H4)) == false
@test mvhsalphaprove(⊤, ∨(parseformula("p"), α), FiniteHeytingAlgebra(H4)) == false
@test mvhsalphaprove(⊤, ∨(parseformula("p"), β), FiniteHeytingAlgebra(H4)) == false
@test mvhsalphaprove(⊤, ∨(parseformula("p"), ⊤), FiniteHeytingAlgebra(H4)) == true

@test mvhsalphaprove(⊥, ∨(⊥, parseformula("p")), FiniteHeytingAlgebra(H4)) == true 
@test mvhsalphaprove(⊥, ∨(α, parseformula("p")), FiniteHeytingAlgebra(H4)) == true 
@test mvhsalphaprove(⊥, ∨(β, parseformula("p")), FiniteHeytingAlgebra(H4)) == true 
@test mvhsalphaprove(⊥, ∨(⊤, parseformula("p")), FiniteHeytingAlgebra(H4)) == true 
@test mvhsalphaprove(α, ∨(⊥, parseformula("p")), FiniteHeytingAlgebra(H4)) == false
@test mvhsalphaprove(α, ∨(α, parseformula("p")), FiniteHeytingAlgebra(H4)) == true 
@test mvhsalphaprove(α, ∨(β, parseformula("p")), FiniteHeytingAlgebra(H4)) == false 
@test mvhsalphaprove(α, ∨(⊤, parseformula("p")), FiniteHeytingAlgebra(H4)) == true 
@test mvhsalphaprove(β, ∨(⊥, parseformula("p")), FiniteHeytingAlgebra(H4)) == false 
@test mvhsalphaprove(β, ∨(α, parseformula("p")), FiniteHeytingAlgebra(H4)) == false 
@test mvhsalphaprove(β, ∨(β, parseformula("p")), FiniteHeytingAlgebra(H4)) == true 
@test mvhsalphaprove(β, ∨(⊤, parseformula("p")), FiniteHeytingAlgebra(H4)) == true 
@test mvhsalphaprove(⊤, ∨(⊥, parseformula("p")), FiniteHeytingAlgebra(H4)) == false 
@test mvhsalphaprove(⊤, ∨(α, parseformula("p")), FiniteHeytingAlgebra(H4)) == false 
@test mvhsalphaprove(⊤, ∨(β, parseformula("p")), FiniteHeytingAlgebra(H4)) == false 
@test mvhsalphaprove(⊤, ∨(⊤, parseformula("p")), FiniteHeytingAlgebra(H4)) == true 

@test mvhsalphaprove(⊥, ∨(parseformula("p"), parseformula("p")), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphaprove(α, ∨(parseformula("p"), parseformula("p")), FiniteHeytingAlgebra(H4)) == false
@test mvhsalphaprove(β, ∨(parseformula("p"), parseformula("p")), FiniteHeytingAlgebra(H4)) == false
@test mvhsalphaprove(⊤, ∨(parseformula("p"), parseformula("p")), FiniteHeytingAlgebra(H4)) == false

@test mvhsalphaprove(⊥, ∨(parseformula("p"), parseformula("q")), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphaprove(α, ∨(parseformula("p"), parseformula("q")), FiniteHeytingAlgebra(H4)) == false
@test mvhsalphaprove(β, ∨(parseformula("p"), parseformula("q")), FiniteHeytingAlgebra(H4)) == false
@test mvhsalphaprove(⊤, ∨(parseformula("p"), parseformula("q")), FiniteHeytingAlgebra(H4)) == false

@test mvhsalphaprove(⊥, ∨(parseformula("q"), parseformula("p")), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphaprove(α, ∨(parseformula("q"), parseformula("p")), FiniteHeytingAlgebra(H4)) == false
@test mvhsalphaprove(β, ∨(parseformula("q"), parseformula("p")), FiniteHeytingAlgebra(H4)) == false
@test mvhsalphaprove(⊤, ∨(parseformula("q"), parseformula("p")), FiniteHeytingAlgebra(H4)) == false

############################################################################################
## (Strong) conjunction ####################################################################
############################################################################################

@test mvhsalphaprove(⊥, ∧(parseformula("p"), ⊥), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphaprove(⊥, ∧(parseformula("p"), α), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphaprove(⊥, ∧(parseformula("p"), β), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphaprove(⊥, ∧(parseformula("p"), ⊤), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphaprove(α, ∧(parseformula("p"), ⊥), FiniteHeytingAlgebra(H4)) == false
@test mvhsalphaprove(α, ∧(parseformula("p"), α), FiniteHeytingAlgebra(H4)) == false
@test mvhsalphaprove(α, ∧(parseformula("p"), β), FiniteHeytingAlgebra(H4)) == false
@test mvhsalphaprove(α, ∧(parseformula("p"), ⊤), FiniteHeytingAlgebra(H4)) == false
@test mvhsalphaprove(β, ∧(parseformula("p"), ⊥), FiniteHeytingAlgebra(H4)) == false
@test mvhsalphaprove(β, ∧(parseformula("p"), α), FiniteHeytingAlgebra(H4)) == false
@test mvhsalphaprove(β, ∧(parseformula("p"), β), FiniteHeytingAlgebra(H4)) == false
@test mvhsalphaprove(β, ∧(parseformula("p"), ⊤), FiniteHeytingAlgebra(H4)) == false
@test mvhsalphaprove(⊤, ∧(parseformula("p"), ⊥), FiniteHeytingAlgebra(H4)) == false
@test mvhsalphaprove(⊤, ∧(parseformula("p"), α), FiniteHeytingAlgebra(H4)) == false
@test mvhsalphaprove(⊤, ∧(parseformula("p"), β), FiniteHeytingAlgebra(H4)) == false
@test mvhsalphaprove(⊤, ∧(parseformula("p"), ⊤), FiniteHeytingAlgebra(H4)) == false

@test mvhsalphaprove(⊥, ∧(⊥, parseformula("p")), FiniteHeytingAlgebra(H4)) == true 
@test mvhsalphaprove(⊥, ∧(α, parseformula("p")), FiniteHeytingAlgebra(H4)) == true 
@test mvhsalphaprove(⊥, ∧(β, parseformula("p")), FiniteHeytingAlgebra(H4)) == true 
@test mvhsalphaprove(⊥, ∧(⊤, parseformula("p")), FiniteHeytingAlgebra(H4)) == true 
@test mvhsalphaprove(α, ∧(⊥, parseformula("p")), FiniteHeytingAlgebra(H4)) == false
@test mvhsalphaprove(α, ∧(α, parseformula("p")), FiniteHeytingAlgebra(H4)) == false 
@test mvhsalphaprove(α, ∧(β, parseformula("p")), FiniteHeytingAlgebra(H4)) == false 
@test mvhsalphaprove(α, ∧(⊤, parseformula("p")), FiniteHeytingAlgebra(H4)) == false 
@test mvhsalphaprove(β, ∧(⊥, parseformula("p")), FiniteHeytingAlgebra(H4)) == false 
@test mvhsalphaprove(β, ∧(α, parseformula("p")), FiniteHeytingAlgebra(H4)) == false 
@test mvhsalphaprove(β, ∧(β, parseformula("p")), FiniteHeytingAlgebra(H4)) == false 
@test mvhsalphaprove(β, ∧(⊤, parseformula("p")), FiniteHeytingAlgebra(H4)) == false 
@test mvhsalphaprove(⊤, ∧(⊥, parseformula("p")), FiniteHeytingAlgebra(H4)) == false 
@test mvhsalphaprove(⊤, ∧(α, parseformula("p")), FiniteHeytingAlgebra(H4)) == false 
@test mvhsalphaprove(⊤, ∧(β, parseformula("p")), FiniteHeytingAlgebra(H4)) == false 
@test mvhsalphaprove(⊤, ∧(⊤, parseformula("p")), FiniteHeytingAlgebra(H4)) == false 

@test mvhsalphaprove(⊥, ∧(parseformula("p"), parseformula("p")), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphaprove(α, ∧(parseformula("p"), parseformula("p")), FiniteHeytingAlgebra(H4)) == false
@test mvhsalphaprove(β, ∧(parseformula("p"), parseformula("p")), FiniteHeytingAlgebra(H4)) == false
@test mvhsalphaprove(⊤, ∧(parseformula("p"), parseformula("p")), FiniteHeytingAlgebra(H4)) == false

@test mvhsalphaprove(⊥, ∧(parseformula("p"), parseformula("q")), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphaprove(α, ∧(parseformula("p"), parseformula("q")), FiniteHeytingAlgebra(H4)) == false
@test mvhsalphaprove(β, ∧(parseformula("p"), parseformula("q")), FiniteHeytingAlgebra(H4)) == false
@test mvhsalphaprove(⊤, ∧(parseformula("p"), parseformula("q")), FiniteHeytingAlgebra(H4)) == false

@test mvhsalphaprove(⊥, ∧(parseformula("q"), parseformula("p")), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphaprove(α, ∧(parseformula("q"), parseformula("p")), FiniteHeytingAlgebra(H4)) == false
@test mvhsalphaprove(β, ∧(parseformula("q"), parseformula("p")), FiniteHeytingAlgebra(H4)) == false
@test mvhsalphaprove(⊤, ∧(parseformula("q"), parseformula("p")), FiniteHeytingAlgebra(H4)) == false

############################################################################################
## Implication #############################################################################
############################################################################################

@test mvhsalphaprove(⊥, →(parseformula("p"), ⊥), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphaprove(⊥, →(parseformula("p"), α), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphaprove(⊥, →(parseformula("p"), β), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphaprove(⊥, →(parseformula("p"), ⊤), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphaprove(α, →(parseformula("p"), ⊥), FiniteHeytingAlgebra(H4)) == false
@test mvhsalphaprove(α, →(parseformula("p"), α), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphaprove(α, →(parseformula("p"), β), FiniteHeytingAlgebra(H4)) == false
@test mvhsalphaprove(α, →(parseformula("p"), ⊤), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphaprove(β, →(parseformula("p"), ⊥), FiniteHeytingAlgebra(H4)) == false
@test mvhsalphaprove(β, →(parseformula("p"), α), FiniteHeytingAlgebra(H4)) == false
@test mvhsalphaprove(β, →(parseformula("p"), β), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphaprove(β, →(parseformula("p"), ⊤), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphaprove(⊤, →(parseformula("p"), ⊥), FiniteHeytingAlgebra(H4)) == false
@test mvhsalphaprove(⊤, →(parseformula("p"), α), FiniteHeytingAlgebra(H4)) == false
@test mvhsalphaprove(⊤, →(parseformula("p"), β), FiniteHeytingAlgebra(H4)) == false
@test mvhsalphaprove(⊤, →(parseformula("p"), ⊤), FiniteHeytingAlgebra(H4)) == true

@test mvhsalphaprove(⊥, →(⊥, parseformula("p")), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphaprove(⊥, →(α, parseformula("p")), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphaprove(⊥, →(β, parseformula("p")), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphaprove(⊥, →(⊤, parseformula("p")), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphaprove(α, →(⊥, parseformula("p")), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphaprove(α, →(α, parseformula("p")), FiniteHeytingAlgebra(H4)) == false
@test mvhsalphaprove(α, →(β, parseformula("p")), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphaprove(α, →(⊤, parseformula("p")), FiniteHeytingAlgebra(H4)) == false
@test mvhsalphaprove(β, →(⊥, parseformula("p")), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphaprove(β, →(α, parseformula("p")), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphaprove(β, →(β, parseformula("p")), FiniteHeytingAlgebra(H4)) == false
@test mvhsalphaprove(β, →(⊤, parseformula("p")), FiniteHeytingAlgebra(H4)) == false
@test mvhsalphaprove(⊤, →(⊥, parseformula("p")), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphaprove(⊤, →(α, parseformula("p")), FiniteHeytingAlgebra(H4)) == false
@test mvhsalphaprove(⊤, →(β, parseformula("p")), FiniteHeytingAlgebra(H4)) == false
@test mvhsalphaprove(⊤, →(⊤, parseformula("p")), FiniteHeytingAlgebra(H4)) == false

@test mvhsalphaprove(⊥, →(parseformula("p"), parseformula("p")), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphaprove(α, →(parseformula("p"), parseformula("p")), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphaprove(β, →(parseformula("p"), parseformula("p")), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphaprove(⊤, →(parseformula("p"), parseformula("p")), FiniteHeytingAlgebra(H4)) == true

@test mvhsalphaprove(⊥, →(parseformula("p"), parseformula("q")), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphaprove(α, →(parseformula("p"), parseformula("q")), FiniteHeytingAlgebra(H4)) == false
@test mvhsalphaprove(β, →(parseformula("p"), parseformula("q")), FiniteHeytingAlgebra(H4)) == false
@test mvhsalphaprove(⊤, →(parseformula("p"), parseformula("q")), FiniteHeytingAlgebra(H4)) == false

@test mvhsalphaprove(⊥, →(parseformula("q"), parseformula("p")), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphaprove(α, →(parseformula("q"), parseformula("p")), FiniteHeytingAlgebra(H4)) == false
@test mvhsalphaprove(β, →(parseformula("q"), parseformula("p")), FiniteHeytingAlgebra(H4)) == false
@test mvhsalphaprove(⊤, →(parseformula("q"), parseformula("p")), FiniteHeytingAlgebra(H4)) == false
