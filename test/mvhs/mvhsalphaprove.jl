max_timeout = 1 # seconds

############################################################################################
#### H4 ####################################################################################
############################################################################################

using SoleLogics.ManyValuedLogics: H4
using SoleLogics.ManyValuedLogics: α, β

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

for i ∈ getdomain(FiniteHeytingAlgebra(H4))
    for j ∈ getdomain(FiniteHeytingAlgebra(H4))
        @test mvhsalphasat(i, j, FiniteHeytingAlgebra(H4), timeout=max_timeout) == mvhsalphaprove(i, j, FiniteHeytingAlgebra(H4), timeout=max_timeout)
        for k ∈ getdomain(FiniteHeytingAlgebra(H4))
            # println("$i\t$j\t$k")
            @test mvhsalphasat(i, ∨(j,k), FiniteHeytingAlgebra(H4), timeout=max_timeout) == mvhsalphaprove(i, ∨(j,k), FiniteHeytingAlgebra(H4), timeout=max_timeout)
            @test mvhsalphasat(i, ∧(j,k), FiniteHeytingAlgebra(H4), timeout=max_timeout) == mvhsalphaprove(i, ∧(j,k), FiniteHeytingAlgebra(H4), timeout=max_timeout)
            @test mvhsalphasat(i, →(j,k), FiniteHeytingAlgebra(H4), timeout=max_timeout) == mvhsalphaprove(i, →(j,k), FiniteHeytingAlgebra(H4), timeout=max_timeout)
        end
    end
end

@test mvhsalphaprove(⊥, parseformula("p"), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphaprove(α, parseformula("p"), FiniteHeytingAlgebra(H4), timeout=max_timeout) == false
@test mvhsalphaprove(β, parseformula("p"), FiniteHeytingAlgebra(H4), timeout=max_timeout) == false
@test mvhsalphaprove(⊤, parseformula("p"), FiniteHeytingAlgebra(H4), timeout=max_timeout) == false

############################################################################################
## (Strong) disjuction #####################################################################
############################################################################################

@test mvhsalphaprove(⊥, ∨(parseformula("p"), ⊥), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphaprove(⊥, ∨(parseformula("p"), α), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphaprove(⊥, ∨(parseformula("p"), β), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphaprove(⊥, ∨(parseformula("p"), ⊤), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphaprove(α, ∨(parseformula("p"), ⊥), FiniteHeytingAlgebra(H4), timeout=max_timeout) == false
@test mvhsalphaprove(α, ∨(parseformula("p"), α), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphaprove(α, ∨(parseformula("p"), β), FiniteHeytingAlgebra(H4), timeout=max_timeout) == false
@test mvhsalphaprove(α, ∨(parseformula("p"), ⊤), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphaprove(β, ∨(parseformula("p"), ⊥), FiniteHeytingAlgebra(H4), timeout=max_timeout) == false
@test mvhsalphaprove(β, ∨(parseformula("p"), α), FiniteHeytingAlgebra(H4), timeout=max_timeout) == false
@test mvhsalphaprove(β, ∨(parseformula("p"), β), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphaprove(β, ∨(parseformula("p"), ⊤), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphaprove(⊤, ∨(parseformula("p"), ⊥), FiniteHeytingAlgebra(H4), timeout=max_timeout) == false
@test mvhsalphaprove(⊤, ∨(parseformula("p"), α), FiniteHeytingAlgebra(H4), timeout=max_timeout) == false
@test mvhsalphaprove(⊤, ∨(parseformula("p"), β), FiniteHeytingAlgebra(H4), timeout=max_timeout) == false
@test mvhsalphaprove(⊤, ∨(parseformula("p"), ⊤), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true

@test mvhsalphaprove(⊥, ∨(⊥, parseformula("p")), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true 
@test mvhsalphaprove(⊥, ∨(α, parseformula("p")), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true 
@test mvhsalphaprove(⊥, ∨(β, parseformula("p")), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true 
@test mvhsalphaprove(⊥, ∨(⊤, parseformula("p")), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true 
@test mvhsalphaprove(α, ∨(⊥, parseformula("p")), FiniteHeytingAlgebra(H4), timeout=max_timeout) == false
@test mvhsalphaprove(α, ∨(α, parseformula("p")), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true 
@test mvhsalphaprove(α, ∨(β, parseformula("p")), FiniteHeytingAlgebra(H4), timeout=max_timeout) == false 
@test mvhsalphaprove(α, ∨(⊤, parseformula("p")), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true 
@test mvhsalphaprove(β, ∨(⊥, parseformula("p")), FiniteHeytingAlgebra(H4), timeout=max_timeout) == false 
@test mvhsalphaprove(β, ∨(α, parseformula("p")), FiniteHeytingAlgebra(H4), timeout=max_timeout) == false 
@test mvhsalphaprove(β, ∨(β, parseformula("p")), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true 
@test mvhsalphaprove(β, ∨(⊤, parseformula("p")), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true 
@test mvhsalphaprove(⊤, ∨(⊥, parseformula("p")), FiniteHeytingAlgebra(H4), timeout=max_timeout) == false 
@test mvhsalphaprove(⊤, ∨(α, parseformula("p")), FiniteHeytingAlgebra(H4), timeout=max_timeout) == false 
@test mvhsalphaprove(⊤, ∨(β, parseformula("p")), FiniteHeytingAlgebra(H4), timeout=max_timeout) == false 
@test mvhsalphaprove(⊤, ∨(⊤, parseformula("p")), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true 

@test mvhsalphaprove(⊥, ∨(parseformula("p"), parseformula("p")), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphaprove(α, ∨(parseformula("p"), parseformula("p")), FiniteHeytingAlgebra(H4), timeout=max_timeout) == false
@test mvhsalphaprove(β, ∨(parseformula("p"), parseformula("p")), FiniteHeytingAlgebra(H4), timeout=max_timeout) == false
@test mvhsalphaprove(⊤, ∨(parseformula("p"), parseformula("p")), FiniteHeytingAlgebra(H4), timeout=max_timeout) == false

@test mvhsalphaprove(⊥, ∨(parseformula("p"), parseformula("q")), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphaprove(α, ∨(parseformula("p"), parseformula("q")), FiniteHeytingAlgebra(H4), timeout=max_timeout) == false
@test mvhsalphaprove(β, ∨(parseformula("p"), parseformula("q")), FiniteHeytingAlgebra(H4), timeout=max_timeout) == false
@test mvhsalphaprove(⊤, ∨(parseformula("p"), parseformula("q")), FiniteHeytingAlgebra(H4), timeout=max_timeout) == false

@test mvhsalphaprove(⊥, ∨(parseformula("q"), parseformula("p")), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphaprove(α, ∨(parseformula("q"), parseformula("p")), FiniteHeytingAlgebra(H4), timeout=max_timeout) == false
@test mvhsalphaprove(β, ∨(parseformula("q"), parseformula("p")), FiniteHeytingAlgebra(H4), timeout=max_timeout) == false
@test mvhsalphaprove(⊤, ∨(parseformula("q"), parseformula("p")), FiniteHeytingAlgebra(H4), timeout=max_timeout) == false

############################################################################################
## (Strong) conjunction ####################################################################
############################################################################################

@test mvhsalphaprove(⊥, ∧(parseformula("p"), ⊥), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphaprove(⊥, ∧(parseformula("p"), α), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphaprove(⊥, ∧(parseformula("p"), β), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphaprove(⊥, ∧(parseformula("p"), ⊤), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphaprove(α, ∧(parseformula("p"), ⊥), FiniteHeytingAlgebra(H4), timeout=max_timeout) == false
@test mvhsalphaprove(α, ∧(parseformula("p"), α), FiniteHeytingAlgebra(H4), timeout=max_timeout) == false
@test mvhsalphaprove(α, ∧(parseformula("p"), β), FiniteHeytingAlgebra(H4), timeout=max_timeout) == false
@test mvhsalphaprove(α, ∧(parseformula("p"), ⊤), FiniteHeytingAlgebra(H4), timeout=max_timeout) == false
@test mvhsalphaprove(β, ∧(parseformula("p"), ⊥), FiniteHeytingAlgebra(H4), timeout=max_timeout) == false
@test mvhsalphaprove(β, ∧(parseformula("p"), α), FiniteHeytingAlgebra(H4), timeout=max_timeout) == false
@test mvhsalphaprove(β, ∧(parseformula("p"), β), FiniteHeytingAlgebra(H4), timeout=max_timeout) == false
@test mvhsalphaprove(β, ∧(parseformula("p"), ⊤), FiniteHeytingAlgebra(H4), timeout=max_timeout) == false
@test mvhsalphaprove(⊤, ∧(parseformula("p"), ⊥), FiniteHeytingAlgebra(H4), timeout=max_timeout) == false
@test mvhsalphaprove(⊤, ∧(parseformula("p"), α), FiniteHeytingAlgebra(H4), timeout=max_timeout) == false
@test mvhsalphaprove(⊤, ∧(parseformula("p"), β), FiniteHeytingAlgebra(H4), timeout=max_timeout) == false
@test mvhsalphaprove(⊤, ∧(parseformula("p"), ⊤), FiniteHeytingAlgebra(H4), timeout=max_timeout) == false

@test mvhsalphaprove(⊥, ∧(⊥, parseformula("p")), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true 
@test mvhsalphaprove(⊥, ∧(α, parseformula("p")), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true 
@test mvhsalphaprove(⊥, ∧(β, parseformula("p")), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true 
@test mvhsalphaprove(⊥, ∧(⊤, parseformula("p")), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true 
@test mvhsalphaprove(α, ∧(⊥, parseformula("p")), FiniteHeytingAlgebra(H4), timeout=max_timeout) == false
@test mvhsalphaprove(α, ∧(α, parseformula("p")), FiniteHeytingAlgebra(H4), timeout=max_timeout) == false 
@test mvhsalphaprove(α, ∧(β, parseformula("p")), FiniteHeytingAlgebra(H4), timeout=max_timeout) == false 
@test mvhsalphaprove(α, ∧(⊤, parseformula("p")), FiniteHeytingAlgebra(H4), timeout=max_timeout) == false 
@test mvhsalphaprove(β, ∧(⊥, parseformula("p")), FiniteHeytingAlgebra(H4), timeout=max_timeout) == false 
@test mvhsalphaprove(β, ∧(α, parseformula("p")), FiniteHeytingAlgebra(H4), timeout=max_timeout) == false 
@test mvhsalphaprove(β, ∧(β, parseformula("p")), FiniteHeytingAlgebra(H4), timeout=max_timeout) == false 
@test mvhsalphaprove(β, ∧(⊤, parseformula("p")), FiniteHeytingAlgebra(H4), timeout=max_timeout) == false 
@test mvhsalphaprove(⊤, ∧(⊥, parseformula("p")), FiniteHeytingAlgebra(H4), timeout=max_timeout) == false 
@test mvhsalphaprove(⊤, ∧(α, parseformula("p")), FiniteHeytingAlgebra(H4), timeout=max_timeout) == false 
@test mvhsalphaprove(⊤, ∧(β, parseformula("p")), FiniteHeytingAlgebra(H4), timeout=max_timeout) == false 
@test mvhsalphaprove(⊤, ∧(⊤, parseformula("p")), FiniteHeytingAlgebra(H4), timeout=max_timeout) == false 

@test mvhsalphaprove(⊥, ∧(parseformula("p"), parseformula("p")), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphaprove(α, ∧(parseformula("p"), parseformula("p")), FiniteHeytingAlgebra(H4), timeout=max_timeout) == false
@test mvhsalphaprove(β, ∧(parseformula("p"), parseformula("p")), FiniteHeytingAlgebra(H4), timeout=max_timeout) == false
@test mvhsalphaprove(⊤, ∧(parseformula("p"), parseformula("p")), FiniteHeytingAlgebra(H4), timeout=max_timeout) == false

@test mvhsalphaprove(⊥, ∧(parseformula("p"), parseformula("q")), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphaprove(α, ∧(parseformula("p"), parseformula("q")), FiniteHeytingAlgebra(H4), timeout=max_timeout) == false
@test mvhsalphaprove(β, ∧(parseformula("p"), parseformula("q")), FiniteHeytingAlgebra(H4), timeout=max_timeout) == false
@test mvhsalphaprove(⊤, ∧(parseformula("p"), parseformula("q")), FiniteHeytingAlgebra(H4), timeout=max_timeout) == false

@test mvhsalphaprove(⊥, ∧(parseformula("q"), parseformula("p")), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphaprove(α, ∧(parseformula("q"), parseformula("p")), FiniteHeytingAlgebra(H4), timeout=max_timeout) == false
@test mvhsalphaprove(β, ∧(parseformula("q"), parseformula("p")), FiniteHeytingAlgebra(H4), timeout=max_timeout) == false
@test mvhsalphaprove(⊤, ∧(parseformula("q"), parseformula("p")), FiniteHeytingAlgebra(H4), timeout=max_timeout) == false

############################################################################################
## Implication #############################################################################
############################################################################################

@test mvhsalphaprove(⊥, →(parseformula("p"), ⊥), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphaprove(⊥, →(parseformula("p"), α), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphaprove(⊥, →(parseformula("p"), β), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphaprove(⊥, →(parseformula("p"), ⊤), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphaprove(α, →(parseformula("p"), ⊥), FiniteHeytingAlgebra(H4), timeout=max_timeout) == false
@test mvhsalphaprove(α, →(parseformula("p"), α), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphaprove(α, →(parseformula("p"), β), FiniteHeytingAlgebra(H4), timeout=max_timeout) == false
@test mvhsalphaprove(α, →(parseformula("p"), ⊤), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphaprove(β, →(parseformula("p"), ⊥), FiniteHeytingAlgebra(H4), timeout=max_timeout) == false
@test mvhsalphaprove(β, →(parseformula("p"), α), FiniteHeytingAlgebra(H4), timeout=max_timeout) == false
@test mvhsalphaprove(β, →(parseformula("p"), β), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphaprove(β, →(parseformula("p"), ⊤), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphaprove(⊤, →(parseformula("p"), ⊥), FiniteHeytingAlgebra(H4), timeout=max_timeout) == false
@test mvhsalphaprove(⊤, →(parseformula("p"), α), FiniteHeytingAlgebra(H4), timeout=max_timeout) == false
@test mvhsalphaprove(⊤, →(parseformula("p"), β), FiniteHeytingAlgebra(H4), timeout=max_timeout) == false
@test mvhsalphaprove(⊤, →(parseformula("p"), ⊤), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true

@test mvhsalphaprove(⊥, →(⊥, parseformula("p")), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphaprove(⊥, →(α, parseformula("p")), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphaprove(⊥, →(β, parseformula("p")), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphaprove(⊥, →(⊤, parseformula("p")), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphaprove(α, →(⊥, parseformula("p")), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphaprove(α, →(α, parseformula("p")), FiniteHeytingAlgebra(H4), timeout=max_timeout) == false
@test mvhsalphaprove(α, →(β, parseformula("p")), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphaprove(α, →(⊤, parseformula("p")), FiniteHeytingAlgebra(H4), timeout=max_timeout) == false
@test mvhsalphaprove(β, →(⊥, parseformula("p")), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphaprove(β, →(α, parseformula("p")), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphaprove(β, →(β, parseformula("p")), FiniteHeytingAlgebra(H4), timeout=max_timeout) == false
@test mvhsalphaprove(β, →(⊤, parseformula("p")), FiniteHeytingAlgebra(H4), timeout=max_timeout) == false
@test mvhsalphaprove(⊤, →(⊥, parseformula("p")), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphaprove(⊤, →(α, parseformula("p")), FiniteHeytingAlgebra(H4), timeout=max_timeout) == false
@test mvhsalphaprove(⊤, →(β, parseformula("p")), FiniteHeytingAlgebra(H4), timeout=max_timeout) == false
@test mvhsalphaprove(⊤, →(⊤, parseformula("p")), FiniteHeytingAlgebra(H4), timeout=max_timeout) == false

@test mvhsalphaprove(⊥, →(parseformula("p"), parseformula("p")), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphaprove(α, →(parseformula("p"), parseformula("p")), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphaprove(β, →(parseformula("p"), parseformula("p")), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphaprove(⊤, →(parseformula("p"), parseformula("p")), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true

@test mvhsalphaprove(⊥, →(parseformula("p"), parseformula("q")), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphaprove(α, →(parseformula("p"), parseformula("q")), FiniteHeytingAlgebra(H4), timeout=max_timeout) == false
@test mvhsalphaprove(β, →(parseformula("p"), parseformula("q")), FiniteHeytingAlgebra(H4), timeout=max_timeout) == false
@test mvhsalphaprove(⊤, →(parseformula("p"), parseformula("q")), FiniteHeytingAlgebra(H4), timeout=max_timeout) == false

@test mvhsalphaprove(⊥, →(parseformula("q"), parseformula("p")), FiniteHeytingAlgebra(H4), timeout=max_timeout) == true
@test mvhsalphaprove(α, →(parseformula("q"), parseformula("p")), FiniteHeytingAlgebra(H4), timeout=max_timeout) == false
@test mvhsalphaprove(β, →(parseformula("q"), parseformula("p")), FiniteHeytingAlgebra(H4), timeout=max_timeout) == false
@test mvhsalphaprove(⊤, →(parseformula("q"), parseformula("p")), FiniteHeytingAlgebra(H4), timeout=max_timeout) == false

############################################################################################
# FLew Algebra #############################################################################
############################################################################################
## Base cases ##############################################################################
############################################################################################

for i ∈ getdomain(H4)
    for j ∈ getdomain(H4)
        @test mvhsalphasat(i, j, H4, timeout=max_timeout) == mvhsalphaprove(i, j, H4, timeout=max_timeout)
        for k ∈ getdomain(H4)
            # println("$i\t$j\t$k")
            @test mvhsalphasat(i, ∨(j,k), H4, timeout=max_timeout) == mvhsalphaprove(i, ∨(j,k), H4, timeout=max_timeout)
            @test mvhsalphasat(i, ∧(j,k), H4, timeout=max_timeout) == mvhsalphaprove(i, ∧(j,k), H4, timeout=max_timeout)
            @test mvhsalphasat(i, →(j,k), H4, timeout=max_timeout) == mvhsalphaprove(i, →(j,k), H4, timeout=max_timeout)
        end
    end
end

@test mvhsalphaprove(⊥, parseformula("p"), H4, timeout=max_timeout) == true
@test mvhsalphaprove(α, parseformula("p"), H4, timeout=max_timeout) == false
@test mvhsalphaprove(β, parseformula("p"), H4, timeout=max_timeout) == false
@test mvhsalphaprove(⊤, parseformula("p"), H4, timeout=max_timeout) == false

############################################################################################
## (Strong) disjuction #####################################################################
############################################################################################

@test mvhsalphaprove(⊥, ∨(parseformula("p"), ⊥), H4, timeout=max_timeout) == true
@test mvhsalphaprove(⊥, ∨(parseformula("p"), α), H4, timeout=max_timeout) == true
@test mvhsalphaprove(⊥, ∨(parseformula("p"), β), H4, timeout=max_timeout) == true
@test mvhsalphaprove(⊥, ∨(parseformula("p"), ⊤), H4, timeout=max_timeout) == true
@test mvhsalphaprove(α, ∨(parseformula("p"), ⊥), H4, timeout=max_timeout) == false
@test mvhsalphaprove(α, ∨(parseformula("p"), α), H4, timeout=max_timeout) == true
@test mvhsalphaprove(α, ∨(parseformula("p"), β), H4, timeout=max_timeout) == false
@test mvhsalphaprove(α, ∨(parseformula("p"), ⊤), H4, timeout=max_timeout) == true
@test mvhsalphaprove(β, ∨(parseformula("p"), ⊥), H4, timeout=max_timeout) == false
@test mvhsalphaprove(β, ∨(parseformula("p"), α), H4, timeout=max_timeout) == false
@test mvhsalphaprove(β, ∨(parseformula("p"), β), H4, timeout=max_timeout) == true
@test mvhsalphaprove(β, ∨(parseformula("p"), ⊤), H4, timeout=max_timeout) == true
@test mvhsalphaprove(⊤, ∨(parseformula("p"), ⊥), H4, timeout=max_timeout) == false
@test mvhsalphaprove(⊤, ∨(parseformula("p"), α), H4, timeout=max_timeout) == false
@test mvhsalphaprove(⊤, ∨(parseformula("p"), β), H4, timeout=max_timeout) == false
@test mvhsalphaprove(⊤, ∨(parseformula("p"), ⊤), H4, timeout=max_timeout) == true

@test mvhsalphaprove(⊥, ∨(⊥, parseformula("p")), H4, timeout=max_timeout) == true 
@test mvhsalphaprove(⊥, ∨(α, parseformula("p")), H4, timeout=max_timeout) == true 
@test mvhsalphaprove(⊥, ∨(β, parseformula("p")), H4, timeout=max_timeout) == true 
@test mvhsalphaprove(⊥, ∨(⊤, parseformula("p")), H4, timeout=max_timeout) == true 
@test mvhsalphaprove(α, ∨(⊥, parseformula("p")), H4, timeout=max_timeout) == false
@test mvhsalphaprove(α, ∨(α, parseformula("p")), H4, timeout=max_timeout) == true 
@test mvhsalphaprove(α, ∨(β, parseformula("p")), H4, timeout=max_timeout) == false 
@test mvhsalphaprove(α, ∨(⊤, parseformula("p")), H4, timeout=max_timeout) == true 
@test mvhsalphaprove(β, ∨(⊥, parseformula("p")), H4, timeout=max_timeout) == false 
@test mvhsalphaprove(β, ∨(α, parseformula("p")), H4, timeout=max_timeout) == false 
@test mvhsalphaprove(β, ∨(β, parseformula("p")), H4, timeout=max_timeout) == true 
@test mvhsalphaprove(β, ∨(⊤, parseformula("p")), H4, timeout=max_timeout) == true 
@test mvhsalphaprove(⊤, ∨(⊥, parseformula("p")), H4, timeout=max_timeout) == false 
@test mvhsalphaprove(⊤, ∨(α, parseformula("p")), H4, timeout=max_timeout) == false 
@test mvhsalphaprove(⊤, ∨(β, parseformula("p")), H4, timeout=max_timeout) == false 
@test mvhsalphaprove(⊤, ∨(⊤, parseformula("p")), H4, timeout=max_timeout) == true 

@test mvhsalphaprove(⊥, ∨(parseformula("p"), parseformula("p")), H4, timeout=max_timeout) == true
@test mvhsalphaprove(α, ∨(parseformula("p"), parseformula("p")), H4, timeout=max_timeout) == false
@test mvhsalphaprove(β, ∨(parseformula("p"), parseformula("p")), H4, timeout=max_timeout) == false
@test mvhsalphaprove(⊤, ∨(parseformula("p"), parseformula("p")), H4, timeout=max_timeout) == false

@test mvhsalphaprove(⊥, ∨(parseformula("p"), parseformula("q")), H4, timeout=max_timeout) == true
@test mvhsalphaprove(α, ∨(parseformula("p"), parseformula("q")), H4, timeout=max_timeout) == false
@test mvhsalphaprove(β, ∨(parseformula("p"), parseformula("q")), H4, timeout=max_timeout) == false
@test mvhsalphaprove(⊤, ∨(parseformula("p"), parseformula("q")), H4, timeout=max_timeout) == false

@test mvhsalphaprove(⊥, ∨(parseformula("q"), parseformula("p")), H4, timeout=max_timeout) == true
@test mvhsalphaprove(α, ∨(parseformula("q"), parseformula("p")), H4, timeout=max_timeout) == false
@test mvhsalphaprove(β, ∨(parseformula("q"), parseformula("p")), H4, timeout=max_timeout) == false
@test mvhsalphaprove(⊤, ∨(parseformula("q"), parseformula("p")), H4, timeout=max_timeout) == false

############################################################################################
## (Strong) conjunction ####################################################################
############################################################################################

@test mvhsalphaprove(⊥, ∧(parseformula("p"), ⊥), H4, timeout=max_timeout) == true
@test mvhsalphaprove(⊥, ∧(parseformula("p"), α), H4, timeout=max_timeout) == true
@test mvhsalphaprove(⊥, ∧(parseformula("p"), β), H4, timeout=max_timeout) == true
@test mvhsalphaprove(⊥, ∧(parseformula("p"), ⊤), H4, timeout=max_timeout) == true
@test mvhsalphaprove(α, ∧(parseformula("p"), ⊥), H4, timeout=max_timeout) == false
@test mvhsalphaprove(α, ∧(parseformula("p"), α), H4, timeout=max_timeout) == false
@test mvhsalphaprove(α, ∧(parseformula("p"), β), H4, timeout=max_timeout) == false
@test mvhsalphaprove(α, ∧(parseformula("p"), ⊤), H4, timeout=max_timeout) == false
@test mvhsalphaprove(β, ∧(parseformula("p"), ⊥), H4, timeout=max_timeout) == false
@test mvhsalphaprove(β, ∧(parseformula("p"), α), H4, timeout=max_timeout) == false
@test mvhsalphaprove(β, ∧(parseformula("p"), β), H4, timeout=max_timeout) == false
@test mvhsalphaprove(β, ∧(parseformula("p"), ⊤), H4, timeout=max_timeout) == false
@test mvhsalphaprove(⊤, ∧(parseformula("p"), ⊥), H4, timeout=max_timeout) == false
@test mvhsalphaprove(⊤, ∧(parseformula("p"), α), H4, timeout=max_timeout) == false
@test mvhsalphaprove(⊤, ∧(parseformula("p"), β), H4, timeout=max_timeout) == false
@test mvhsalphaprove(⊤, ∧(parseformula("p"), ⊤), H4, timeout=max_timeout) == false

@test mvhsalphaprove(⊥, ∧(⊥, parseformula("p")), H4, timeout=max_timeout) == true 
@test mvhsalphaprove(⊥, ∧(α, parseformula("p")), H4, timeout=max_timeout) == true 
@test mvhsalphaprove(⊥, ∧(β, parseformula("p")), H4, timeout=max_timeout) == true 
@test mvhsalphaprove(⊥, ∧(⊤, parseformula("p")), H4, timeout=max_timeout) == true 
@test mvhsalphaprove(α, ∧(⊥, parseformula("p")), H4, timeout=max_timeout) == false
@test mvhsalphaprove(α, ∧(α, parseformula("p")), H4, timeout=max_timeout) == false 
@test mvhsalphaprove(α, ∧(β, parseformula("p")), H4, timeout=max_timeout) == false 
@test mvhsalphaprove(α, ∧(⊤, parseformula("p")), H4, timeout=max_timeout) == false 
@test mvhsalphaprove(β, ∧(⊥, parseformula("p")), H4, timeout=max_timeout) == false 
@test mvhsalphaprove(β, ∧(α, parseformula("p")), H4, timeout=max_timeout) == false 
@test mvhsalphaprove(β, ∧(β, parseformula("p")), H4, timeout=max_timeout) == false 
@test mvhsalphaprove(β, ∧(⊤, parseformula("p")), H4, timeout=max_timeout) == false 
@test mvhsalphaprove(⊤, ∧(⊥, parseformula("p")), H4, timeout=max_timeout) == false 
@test mvhsalphaprove(⊤, ∧(α, parseformula("p")), H4, timeout=max_timeout) == false 
@test mvhsalphaprove(⊤, ∧(β, parseformula("p")), H4, timeout=max_timeout) == false 
@test mvhsalphaprove(⊤, ∧(⊤, parseformula("p")), H4, timeout=max_timeout) == false 

@test mvhsalphaprove(⊥, ∧(parseformula("p"), parseformula("p")), H4, timeout=max_timeout) == true
@test mvhsalphaprove(α, ∧(parseformula("p"), parseformula("p")), H4, timeout=max_timeout) == false
@test mvhsalphaprove(β, ∧(parseformula("p"), parseformula("p")), H4, timeout=max_timeout) == false
@test mvhsalphaprove(⊤, ∧(parseformula("p"), parseformula("p")), H4, timeout=max_timeout) == false

@test mvhsalphaprove(⊥, ∧(parseformula("p"), parseformula("q")), H4, timeout=max_timeout) == true
@test mvhsalphaprove(α, ∧(parseformula("p"), parseformula("q")), H4, timeout=max_timeout) == false
@test mvhsalphaprove(β, ∧(parseformula("p"), parseformula("q")), H4, timeout=max_timeout) == false
@test mvhsalphaprove(⊤, ∧(parseformula("p"), parseformula("q")), H4, timeout=max_timeout) == false

@test mvhsalphaprove(⊥, ∧(parseformula("q"), parseformula("p")), H4, timeout=max_timeout) == true
@test mvhsalphaprove(α, ∧(parseformula("q"), parseformula("p")), H4, timeout=max_timeout) == false
@test mvhsalphaprove(β, ∧(parseformula("q"), parseformula("p")), H4, timeout=max_timeout) == false
@test mvhsalphaprove(⊤, ∧(parseformula("q"), parseformula("p")), H4, timeout=max_timeout) == false

############################################################################################
## Implication #############################################################################
############################################################################################

@test mvhsalphaprove(⊥, →(parseformula("p"), ⊥), H4, timeout=max_timeout) == true
@test mvhsalphaprove(⊥, →(parseformula("p"), α), H4, timeout=max_timeout) == true
@test mvhsalphaprove(⊥, →(parseformula("p"), β), H4, timeout=max_timeout) == true
@test mvhsalphaprove(⊥, →(parseformula("p"), ⊤), H4, timeout=max_timeout) == true
@test mvhsalphaprove(α, →(parseformula("p"), ⊥), H4, timeout=max_timeout) == false
@test mvhsalphaprove(α, →(parseformula("p"), α), H4, timeout=max_timeout) == true
@test mvhsalphaprove(α, →(parseformula("p"), β), H4, timeout=max_timeout) == false
@test mvhsalphaprove(α, →(parseformula("p"), ⊤), H4, timeout=max_timeout) == true
@test mvhsalphaprove(β, →(parseformula("p"), ⊥), H4, timeout=max_timeout) == false
@test mvhsalphaprove(β, →(parseformula("p"), α), H4, timeout=max_timeout) == false
@test mvhsalphaprove(β, →(parseformula("p"), β), H4, timeout=max_timeout) == true
@test mvhsalphaprove(β, →(parseformula("p"), ⊤), H4, timeout=max_timeout) == true
@test mvhsalphaprove(⊤, →(parseformula("p"), ⊥), H4, timeout=max_timeout) == false
@test mvhsalphaprove(⊤, →(parseformula("p"), α), H4, timeout=max_timeout) == false
@test mvhsalphaprove(⊤, →(parseformula("p"), β), H4, timeout=max_timeout) == false
@test mvhsalphaprove(⊤, →(parseformula("p"), ⊤), H4, timeout=max_timeout) == true

@test mvhsalphaprove(⊥, →(⊥, parseformula("p")), H4, timeout=max_timeout) == true
@test mvhsalphaprove(⊥, →(α, parseformula("p")), H4, timeout=max_timeout) == true
@test mvhsalphaprove(⊥, →(β, parseformula("p")), H4, timeout=max_timeout) == true
@test mvhsalphaprove(⊥, →(⊤, parseformula("p")), H4, timeout=max_timeout) == true
@test mvhsalphaprove(α, →(⊥, parseformula("p")), H4, timeout=max_timeout) == true
@test mvhsalphaprove(α, →(α, parseformula("p")), H4, timeout=max_timeout) == false
@test mvhsalphaprove(α, →(β, parseformula("p")), H4, timeout=max_timeout) == true
@test mvhsalphaprove(α, →(⊤, parseformula("p")), H4, timeout=max_timeout) == false
@test mvhsalphaprove(β, →(⊥, parseformula("p")), H4, timeout=max_timeout) == true
@test mvhsalphaprove(β, →(α, parseformula("p")), H4, timeout=max_timeout) == true
@test mvhsalphaprove(β, →(β, parseformula("p")), H4, timeout=max_timeout) == false
@test mvhsalphaprove(β, →(⊤, parseformula("p")), H4, timeout=max_timeout) == false
@test mvhsalphaprove(⊤, →(⊥, parseformula("p")), H4, timeout=max_timeout) == true
@test mvhsalphaprove(⊤, →(α, parseformula("p")), H4, timeout=max_timeout) == false
@test mvhsalphaprove(⊤, →(β, parseformula("p")), H4, timeout=max_timeout) == false
@test mvhsalphaprove(⊤, →(⊤, parseformula("p")), H4, timeout=max_timeout) == false

@test mvhsalphaprove(⊥, →(parseformula("p"), parseformula("p")), H4, timeout=max_timeout) == true
@test mvhsalphaprove(α, →(parseformula("p"), parseformula("p")), H4, timeout=max_timeout) == true
@test mvhsalphaprove(β, →(parseformula("p"), parseformula("p")), H4, timeout=max_timeout) == true
@test mvhsalphaprove(⊤, →(parseformula("p"), parseformula("p")), H4, timeout=max_timeout) == true

@test mvhsalphaprove(⊥, →(parseformula("p"), parseformula("q")), H4, timeout=max_timeout) == true
@test mvhsalphaprove(α, →(parseformula("p"), parseformula("q")), H4, timeout=max_timeout) == false
@test mvhsalphaprove(β, →(parseformula("p"), parseformula("q")), H4, timeout=max_timeout) == false
@test mvhsalphaprove(⊤, →(parseformula("p"), parseformula("q")), H4, timeout=max_timeout) == false

@test mvhsalphaprove(⊥, →(parseformula("q"), parseformula("p")), H4, timeout=max_timeout) == true
@test mvhsalphaprove(α, →(parseformula("q"), parseformula("p")), H4, timeout=max_timeout) == false
@test mvhsalphaprove(β, →(parseformula("q"), parseformula("p")), H4, timeout=max_timeout) == false
@test mvhsalphaprove(⊤, →(parseformula("q"), parseformula("p")), H4, timeout=max_timeout) == false
