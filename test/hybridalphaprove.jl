############################################################################################
#### G4 ####################################################################################
############################################################################################

using SoleLogics.ManyValuedLogics: G4
using SoleLogics.ManyValuedLogics: α, β

############################################################################################
## Base cases ##############################################################################
############################################################################################

for i ∈ getdomain(G4)
    for j ∈ getdomain(G4)
        @test hybridalphasat(i, j, G4) == hybridalphaprove(i, j, G4)
        for k ∈ getdomain(G4)
            @test hybridalphasat(i, ∨(j,k), G4) == hybridalphaprove(i, ∨(j,k), G4)
            @test hybridalphasat(i, ∧(j,k), G4) == hybridalphaprove(i, ∧(j,k), G4)
            @test hybridalphasat(i, →(j,k), G4) == hybridalphaprove(i, →(j,k), G4)
        end
    end
end

@test hybridalphaprove(⊥, parseformula("p"), G4) == true
@test hybridalphaprove(α, parseformula("p"), G4) == false
@test hybridalphaprove(β, parseformula("p"), G4) == false
@test hybridalphaprove(⊤, parseformula("p"), G4) == false

############################################################################################
## (Strong) disjunction ####################################################################
############################################################################################

@test hybridalphaprove(⊥, ∨(parseformula("p"), ⊥), G4) == true
@test hybridalphaprove(⊥, ∨(parseformula("p"), α), G4) == true
@test hybridalphaprove(⊥, ∨(parseformula("p"), β), G4) == true
@test hybridalphaprove(⊥, ∨(parseformula("p"), ⊤), G4) == true
@test hybridalphaprove(α, ∨(parseformula("p"), ⊥), G4) == false
@test hybridalphaprove(α, ∨(parseformula("p"), α), G4) == true
@test hybridalphaprove(α, ∨(parseformula("p"), β), G4) == true
@test hybridalphaprove(α, ∨(parseformula("p"), ⊤), G4) == true
@test hybridalphaprove(β, ∨(parseformula("p"), ⊥), G4) == false
@test hybridalphaprove(β, ∨(parseformula("p"), α), G4) == false
@test hybridalphaprove(β, ∨(parseformula("p"), β), G4) == true
@test hybridalphaprove(β, ∨(parseformula("p"), ⊤), G4) == true
@test hybridalphaprove(⊤, ∨(parseformula("p"), ⊥), G4) == false
@test hybridalphaprove(⊤, ∨(parseformula("p"), α), G4) == false
@test hybridalphaprove(⊤, ∨(parseformula("p"), β), G4) == false
@test hybridalphaprove(⊤, ∨(parseformula("p"), ⊤), G4) == true

@test hybridalphaprove(⊥, ∨(⊥, parseformula("p")), G4) == true
@test hybridalphaprove(⊥, ∨(α, parseformula("p")), G4) == true 
@test hybridalphaprove(⊥, ∨(β, parseformula("p")), G4) == true 
@test hybridalphaprove(⊥, ∨(⊤, parseformula("p")), G4) == true 
@test hybridalphaprove(α, ∨(⊥, parseformula("p")), G4) == false
@test hybridalphaprove(α, ∨(α, parseformula("p")), G4) == true 
@test hybridalphaprove(α, ∨(β, parseformula("p")), G4) == true 
@test hybridalphaprove(α, ∨(⊤, parseformula("p")), G4) == true 
@test hybridalphaprove(β, ∨(⊥, parseformula("p")), G4) == false 
@test hybridalphaprove(β, ∨(α, parseformula("p")), G4) == false 
@test hybridalphaprove(β, ∨(β, parseformula("p")), G4) == true 
@test hybridalphaprove(β, ∨(⊤, parseformula("p")), G4) == true 
@test hybridalphaprove(⊤, ∨(⊥, parseformula("p")), G4) == false 
@test hybridalphaprove(⊤, ∨(α, parseformula("p")), G4) == false 
@test hybridalphaprove(⊤, ∨(β, parseformula("p")), G4) == false 
@test hybridalphaprove(⊤, ∨(⊤, parseformula("p")), G4) == true 

@test hybridalphaprove(⊥, ∨(parseformula("p"), parseformula("p")), G4) == true
@test hybridalphaprove(α, ∨(parseformula("p"), parseformula("p")), G4) == false
@test hybridalphaprove(β, ∨(parseformula("p"), parseformula("p")), G4) == false
@test hybridalphaprove(⊤, ∨(parseformula("p"), parseformula("p")), G4) == false

@test hybridalphaprove(⊥, ∨(parseformula("p"), parseformula("q")), G4) == true
@test hybridalphaprove(α, ∨(parseformula("p"), parseformula("q")), G4) == false
@test hybridalphaprove(β, ∨(parseformula("p"), parseformula("q")), G4) == false
@test hybridalphaprove(⊤, ∨(parseformula("p"), parseformula("q")), G4) == false

@test hybridalphaprove(⊥, ∨(parseformula("q"), parseformula("p")), G4) == true
@test hybridalphaprove(α, ∨(parseformula("q"), parseformula("p")), G4) == false
@test hybridalphaprove(β, ∨(parseformula("q"), parseformula("p")), G4) == false
@test hybridalphaprove(⊤, ∨(parseformula("q"), parseformula("p")), G4) == false

############################################################################################
## (Strong) conjunction ####################################################################
############################################################################################

@test hybridalphaprove(⊥, ∧(parseformula("p"), ⊥), G4) == true
@test hybridalphaprove(⊥, ∧(parseformula("p"), α), G4) == true
@test hybridalphaprove(⊥, ∧(parseformula("p"), β), G4) == true
@test hybridalphaprove(⊥, ∧(parseformula("p"), ⊤), G4) == true
@test hybridalphaprove(α, ∧(parseformula("p"), ⊥), G4) == false
@test hybridalphaprove(α, ∧(parseformula("p"), α), G4) == false
@test hybridalphaprove(α, ∧(parseformula("p"), β), G4) == false
@test hybridalphaprove(α, ∧(parseformula("p"), ⊤), G4) == false
@test hybridalphaprove(β, ∧(parseformula("p"), ⊥), G4) == false
@test hybridalphaprove(β, ∧(parseformula("p"), α), G4) == false
@test hybridalphaprove(β, ∧(parseformula("p"), β), G4) == false
@test hybridalphaprove(β, ∧(parseformula("p"), ⊤), G4) == false
@test hybridalphaprove(⊤, ∧(parseformula("p"), ⊥), G4) == false
@test hybridalphaprove(⊤, ∧(parseformula("p"), α), G4) == false
@test hybridalphaprove(⊤, ∧(parseformula("p"), β), G4) == false
@test hybridalphaprove(⊤, ∧(parseformula("p"), ⊤), G4) == false

@test hybridalphaprove(⊥, ∧(⊥, parseformula("p")), G4) == true 
@test hybridalphaprove(⊥, ∧(α, parseformula("p")), G4) == true 
@test hybridalphaprove(⊥, ∧(β, parseformula("p")), G4) == true 
@test hybridalphaprove(⊥, ∧(⊤, parseformula("p")), G4) == true 
@test hybridalphaprove(α, ∧(⊥, parseformula("p")), G4) == false
@test hybridalphaprove(α, ∧(α, parseformula("p")), G4) == false 
@test hybridalphaprove(α, ∧(β, parseformula("p")), G4) == false 
@test hybridalphaprove(α, ∧(⊤, parseformula("p")), G4) == false 
@test hybridalphaprove(β, ∧(⊥, parseformula("p")), G4) == false 
@test hybridalphaprove(β, ∧(α, parseformula("p")), G4) == false 
@test hybridalphaprove(β, ∧(β, parseformula("p")), G4) == false 
@test hybridalphaprove(β, ∧(⊤, parseformula("p")), G4) == false 
@test hybridalphaprove(⊤, ∧(⊥, parseformula("p")), G4) == false 
@test hybridalphaprove(⊤, ∧(α, parseformula("p")), G4) == false 
@test hybridalphaprove(⊤, ∧(β, parseformula("p")), G4) == false 
@test hybridalphaprove(⊤, ∧(⊤, parseformula("p")), G4) == false 

@test hybridalphaprove(⊥, ∧(parseformula("p"), parseformula("p")), G4) == true
@test hybridalphaprove(α, ∧(parseformula("p"), parseformula("p")), G4) == false
@test hybridalphaprove(β, ∧(parseformula("p"), parseformula("p")), G4) == false
@test hybridalphaprove(⊤, ∧(parseformula("p"), parseformula("p")), G4) == false

@test hybridalphaprove(⊥, ∧(parseformula("p"), parseformula("q")), G4) == true
@test hybridalphaprove(α, ∧(parseformula("p"), parseformula("q")), G4) == false
@test hybridalphaprove(β, ∧(parseformula("p"), parseformula("q")), G4) == false
@test hybridalphaprove(⊤, ∧(parseformula("p"), parseformula("q")), G4) == false

@test hybridalphaprove(⊥, ∧(parseformula("q"), parseformula("p")), G4) == true
@test hybridalphaprove(α, ∧(parseformula("q"), parseformula("p")), G4) == false
@test hybridalphaprove(β, ∧(parseformula("q"), parseformula("p")), G4) == false
@test hybridalphaprove(⊤, ∧(parseformula("q"), parseformula("p")), G4) == false

############################################################################################
## Implication #############################################################################
############################################################################################

@test hybridalphaprove(⊥, →(parseformula("p"), ⊥), G4) == true
@test hybridalphaprove(⊥, →(parseformula("p"), α), G4) == true
@test hybridalphaprove(⊥, →(parseformula("p"), β), G4) == true
@test hybridalphaprove(⊥, →(parseformula("p"), ⊤), G4) == true
@test hybridalphaprove(α, →(parseformula("p"), ⊥), G4) == false
@test hybridalphaprove(α, →(parseformula("p"), α), G4) == true
@test hybridalphaprove(α, →(parseformula("p"), β), G4) == true
@test hybridalphaprove(α, →(parseformula("p"), ⊤), G4) == true
@test hybridalphaprove(β, →(parseformula("p"), ⊥), G4) == false
@test hybridalphaprove(β, →(parseformula("p"), α), G4) == false
@test hybridalphaprove(β, →(parseformula("p"), β), G4) == true
@test hybridalphaprove(β, →(parseformula("p"), ⊤), G4) == true
@test hybridalphaprove(⊤, →(parseformula("p"), ⊥), G4) == false
@test hybridalphaprove(⊤, →(parseformula("p"), α), G4) == false
@test hybridalphaprove(⊤, →(parseformula("p"), β), G4) == false
@test hybridalphaprove(⊤, →(parseformula("p"), ⊤), G4) == true

@test hybridalphaprove(⊥, →(⊥, parseformula("p")), G4) == true
@test hybridalphaprove(⊥, →(α, parseformula("p")), G4) == true
@test hybridalphaprove(⊥, →(β, parseformula("p")), G4) == true
@test hybridalphaprove(⊥, →(⊤, parseformula("p")), G4) == true
@test hybridalphaprove(α, →(⊥, parseformula("p")), G4) == true
@test hybridalphaprove(α, →(α, parseformula("p")), G4) == false
@test hybridalphaprove(α, →(β, parseformula("p")), G4) == false
@test hybridalphaprove(α, →(⊤, parseformula("p")), G4) == false
@test hybridalphaprove(β, →(⊥, parseformula("p")), G4) == true
@test hybridalphaprove(β, →(α, parseformula("p")), G4) == false
@test hybridalphaprove(β, →(β, parseformula("p")), G4) == false
@test hybridalphaprove(β, →(⊤, parseformula("p")), G4) == false
@test hybridalphaprove(⊤, →(⊥, parseformula("p")), G4) == true
@test hybridalphaprove(⊤, →(α, parseformula("p")), G4) == false
@test hybridalphaprove(⊤, →(β, parseformula("p")), G4) == false
@test hybridalphaprove(⊤, →(⊤, parseformula("p")), G4) == false

@test hybridalphaprove(⊥, →(parseformula("p"), parseformula("p")), G4) == true
@test hybridalphaprove(α, →(parseformula("p"), parseformula("p")), G4) == true
@test hybridalphaprove(β, →(parseformula("p"), parseformula("p")), G4) == true
@test hybridalphaprove(⊤, →(parseformula("p"), parseformula("p")), G4) == true

@test hybridalphaprove(⊥, →(parseformula("p"), parseformula("q")), G4) == true
@test hybridalphaprove(α, →(parseformula("p"), parseformula("q")), G4) == false
@test hybridalphaprove(β, →(parseformula("p"), parseformula("q")), G4) == false
@test hybridalphaprove(⊤, →(parseformula("p"), parseformula("q")), G4) == false

@test hybridalphaprove(⊥, →(parseformula("q"), parseformula("p")), G4) == true
@test hybridalphaprove(α, →(parseformula("q"), parseformula("p")), G4) == false
@test hybridalphaprove(β, →(parseformula("q"), parseformula("p")), G4) == false
@test hybridalphaprove(⊤, →(parseformula("q"), parseformula("p")), G4) == false

############################################################################################
#### Ł4 ####################################################################################
############################################################################################

using SoleLogics.ManyValuedLogics: Ł4
using SoleLogics.ManyValuedLogics: α, β

############################################################################################
## Base cases ##############################################################################
############################################################################################

for i ∈ getdomain(Ł4)
    for j ∈ getdomain(Ł4)
        @test hybridalphasat(i, j, Ł4) == hybridalphaprove(i, j, Ł4)
        for k ∈ getdomain(Ł4)
            @test hybridalphasat(i, ∨(j,k), Ł4) == hybridalphaprove(i, ∨(j,k), Ł4)
            @test hybridalphasat(i, ∧(j,k), Ł4) == hybridalphaprove(i, ∧(j,k), Ł4)
            @test hybridalphasat(i, →(j,k), Ł4) == hybridalphaprove(i, →(j,k), Ł4)
        end
    end
end

@test hybridalphaprove(⊥, parseformula("p"), Ł4) == true
@test hybridalphaprove(α, parseformula("p"), Ł4) == false
@test hybridalphaprove(β, parseformula("p"), Ł4) == false
@test hybridalphaprove(⊤, parseformula("p"), Ł4) == false

############################################################################################
## (Strong) disjunction ####################################################################
############################################################################################

@test hybridalphaprove(⊥, ∨(parseformula("p"), ⊥), Ł4) == true
@test hybridalphaprove(⊥, ∨(parseformula("p"), α), Ł4) == true
@test hybridalphaprove(⊥, ∨(parseformula("p"), β), Ł4) == true
@test hybridalphaprove(⊥, ∨(parseformula("p"), ⊤), Ł4) == true
@test hybridalphaprove(α, ∨(parseformula("p"), ⊥), Ł4) == false
@test hybridalphaprove(α, ∨(parseformula("p"), α), Ł4) == true
@test hybridalphaprove(α, ∨(parseformula("p"), β), Ł4) == true
@test hybridalphaprove(α, ∨(parseformula("p"), ⊤), Ł4) == true
@test hybridalphaprove(β, ∨(parseformula("p"), ⊥), Ł4) == false
@test hybridalphaprove(β, ∨(parseformula("p"), α), Ł4) == false
@test hybridalphaprove(β, ∨(parseformula("p"), β), Ł4) == true
@test hybridalphaprove(β, ∨(parseformula("p"), ⊤), Ł4) == true
@test hybridalphaprove(⊤, ∨(parseformula("p"), ⊥), Ł4) == false
@test hybridalphaprove(⊤, ∨(parseformula("p"), α), Ł4) == false
@test hybridalphaprove(⊤, ∨(parseformula("p"), β), Ł4) == false
@test hybridalphaprove(⊤, ∨(parseformula("p"), ⊤), Ł4) == true

@test hybridalphaprove(⊥, ∨(⊥, parseformula("p")), Ł4) == true
@test hybridalphaprove(⊥, ∨(α, parseformula("p")), Ł4) == true 
@test hybridalphaprove(⊥, ∨(β, parseformula("p")), Ł4) == true 
@test hybridalphaprove(⊥, ∨(⊤, parseformula("p")), Ł4) == true 
@test hybridalphaprove(α, ∨(⊥, parseformula("p")), Ł4) == false
@test hybridalphaprove(α, ∨(α, parseformula("p")), Ł4) == true 
@test hybridalphaprove(α, ∨(β, parseformula("p")), Ł4) == true 
@test hybridalphaprove(α, ∨(⊤, parseformula("p")), Ł4) == true 
@test hybridalphaprove(β, ∨(⊥, parseformula("p")), Ł4) == false 
@test hybridalphaprove(β, ∨(α, parseformula("p")), Ł4) == false 
@test hybridalphaprove(β, ∨(β, parseformula("p")), Ł4) == true 
@test hybridalphaprove(β, ∨(⊤, parseformula("p")), Ł4) == true 
@test hybridalphaprove(⊤, ∨(⊥, parseformula("p")), Ł4) == false 
@test hybridalphaprove(⊤, ∨(α, parseformula("p")), Ł4) == false 
@test hybridalphaprove(⊤, ∨(β, parseformula("p")), Ł4) == false 
@test hybridalphaprove(⊤, ∨(⊤, parseformula("p")), Ł4) == true 

@test hybridalphaprove(⊥, ∨(parseformula("p"), parseformula("p")), Ł4) == true
@test hybridalphaprove(α, ∨(parseformula("p"), parseformula("p")), Ł4) == false
@test hybridalphaprove(β, ∨(parseformula("p"), parseformula("p")), Ł4) == false
@test hybridalphaprove(⊤, ∨(parseformula("p"), parseformula("p")), Ł4) == false

@test hybridalphaprove(⊥, ∨(parseformula("p"), parseformula("q")), Ł4) == true
@test hybridalphaprove(α, ∨(parseformula("p"), parseformula("q")), Ł4) == false
@test hybridalphaprove(β, ∨(parseformula("p"), parseformula("q")), Ł4) == false
@test hybridalphaprove(⊤, ∨(parseformula("p"), parseformula("q")), Ł4) == false

@test hybridalphaprove(⊥, ∨(parseformula("q"), parseformula("p")), Ł4) == true
@test hybridalphaprove(α, ∨(parseformula("q"), parseformula("p")), Ł4) == false
@test hybridalphaprove(β, ∨(parseformula("q"), parseformula("p")), Ł4) == false
@test hybridalphaprove(⊤, ∨(parseformula("q"), parseformula("p")), Ł4) == false

############################################################################################
## (Strong) conjunction ####################################################################
############################################################################################

@test hybridalphaprove(⊥, ∧(parseformula("p"), ⊥), Ł4) == true
@test hybridalphaprove(⊥, ∧(parseformula("p"), α), Ł4) == true
@test hybridalphaprove(⊥, ∧(parseformula("p"), β), Ł4) == true
@test hybridalphaprove(⊥, ∧(parseformula("p"), ⊤), Ł4) == true
@test hybridalphaprove(α, ∧(parseformula("p"), ⊥), Ł4) == false
@test hybridalphaprove(α, ∧(parseformula("p"), α), Ł4) == false
@test hybridalphaprove(α, ∧(parseformula("p"), β), Ł4) == false
@test hybridalphaprove(α, ∧(parseformula("p"), ⊤), Ł4) == false
@test hybridalphaprove(β, ∧(parseformula("p"), ⊥), Ł4) == false
@test hybridalphaprove(β, ∧(parseformula("p"), α), Ł4) == false
@test hybridalphaprove(β, ∧(parseformula("p"), β), Ł4) == false
@test hybridalphaprove(β, ∧(parseformula("p"), ⊤), Ł4) == false
@test hybridalphaprove(⊤, ∧(parseformula("p"), ⊥), Ł4) == false
@test hybridalphaprove(⊤, ∧(parseformula("p"), α), Ł4) == false
@test hybridalphaprove(⊤, ∧(parseformula("p"), β), Ł4) == false
@test hybridalphaprove(⊤, ∧(parseformula("p"), ⊤), Ł4) == false

@test hybridalphaprove(⊥, ∧(⊥, parseformula("p")), Ł4) == true 
@test hybridalphaprove(⊥, ∧(α, parseformula("p")), Ł4) == true 
@test hybridalphaprove(⊥, ∧(β, parseformula("p")), Ł4) == true 
@test hybridalphaprove(⊥, ∧(⊤, parseformula("p")), Ł4) == true 
@test hybridalphaprove(α, ∧(⊥, parseformula("p")), Ł4) == false
@test hybridalphaprove(α, ∧(α, parseformula("p")), Ł4) == false 
@test hybridalphaprove(α, ∧(β, parseformula("p")), Ł4) == false 
@test hybridalphaprove(α, ∧(⊤, parseformula("p")), Ł4) == false 
@test hybridalphaprove(β, ∧(⊥, parseformula("p")), Ł4) == false 
@test hybridalphaprove(β, ∧(α, parseformula("p")), Ł4) == false 
@test hybridalphaprove(β, ∧(β, parseformula("p")), Ł4) == false 
@test hybridalphaprove(β, ∧(⊤, parseformula("p")), Ł4) == false 
@test hybridalphaprove(⊤, ∧(⊥, parseformula("p")), Ł4) == false 
@test hybridalphaprove(⊤, ∧(α, parseformula("p")), Ł4) == false 
@test hybridalphaprove(⊤, ∧(β, parseformula("p")), Ł4) == false 
@test hybridalphaprove(⊤, ∧(⊤, parseformula("p")), Ł4) == false 

@test hybridalphaprove(⊥, ∧(parseformula("p"), parseformula("p")), Ł4) == true
@test hybridalphaprove(α, ∧(parseformula("p"), parseformula("p")), Ł4) == false
@test hybridalphaprove(β, ∧(parseformula("p"), parseformula("p")), Ł4) == false
@test hybridalphaprove(⊤, ∧(parseformula("p"), parseformula("p")), Ł4) == false

@test hybridalphaprove(⊥, ∧(parseformula("p"), parseformula("q")), Ł4) == true
@test hybridalphaprove(α, ∧(parseformula("p"), parseformula("q")), Ł4) == false
@test hybridalphaprove(β, ∧(parseformula("p"), parseformula("q")), Ł4) == false
@test hybridalphaprove(⊤, ∧(parseformula("p"), parseformula("q")), Ł4) == false

@test hybridalphaprove(⊥, ∧(parseformula("q"), parseformula("p")), Ł4) == true
@test hybridalphaprove(α, ∧(parseformula("q"), parseformula("p")), Ł4) == false
@test hybridalphaprove(β, ∧(parseformula("q"), parseformula("p")), Ł4) == false
@test hybridalphaprove(⊤, ∧(parseformula("q"), parseformula("p")), Ł4) == false

############################################################################################
## Implication #############################################################################
############################################################################################

@test hybridalphaprove(⊥, →(parseformula("p"), ⊥), Ł4) == true
@test hybridalphaprove(⊥, →(parseformula("p"), α), Ł4) == true
@test hybridalphaprove(⊥, →(parseformula("p"), β), Ł4) == true
@test hybridalphaprove(⊥, →(parseformula("p"), ⊤), Ł4) == true
@test hybridalphaprove(α, →(parseformula("p"), ⊥), Ł4) == false
@test hybridalphaprove(α, →(parseformula("p"), α), Ł4) == true
@test hybridalphaprove(α, →(parseformula("p"), β), Ł4) == true
@test hybridalphaprove(α, →(parseformula("p"), ⊤), Ł4) == true
@test hybridalphaprove(β, →(parseformula("p"), ⊥), Ł4) == false
@test hybridalphaprove(β, →(parseformula("p"), α), Ł4) == false
@test hybridalphaprove(β, →(parseformula("p"), β), Ł4) == true
@test hybridalphaprove(β, →(parseformula("p"), ⊤), Ł4) == true
@test hybridalphaprove(⊤, →(parseformula("p"), ⊥), Ł4) == false
@test hybridalphaprove(⊤, →(parseformula("p"), α), Ł4) == false
@test hybridalphaprove(⊤, →(parseformula("p"), β), Ł4) == false
@test hybridalphaprove(⊤, →(parseformula("p"), ⊤), Ł4) == true

@test hybridalphaprove(⊥, →(⊥, parseformula("p")), Ł4) == true
@test hybridalphaprove(⊥, →(α, parseformula("p")), Ł4) == true
@test hybridalphaprove(⊥, →(β, parseformula("p")), Ł4) == true
@test hybridalphaprove(⊥, →(⊤, parseformula("p")), Ł4) == true
@test hybridalphaprove(α, →(⊥, parseformula("p")), Ł4) == true
@test hybridalphaprove(α, →(α, parseformula("p")), Ł4) == true
@test hybridalphaprove(α, →(β, parseformula("p")), Ł4) == true
@test hybridalphaprove(α, →(⊤, parseformula("p")), Ł4) == false
@test hybridalphaprove(β, →(⊥, parseformula("p")), Ł4) == true
@test hybridalphaprove(β, →(α, parseformula("p")), Ł4) == true
@test hybridalphaprove(β, →(β, parseformula("p")), Ł4) == false
@test hybridalphaprove(β, →(⊤, parseformula("p")), Ł4) == false
@test hybridalphaprove(⊤, →(⊥, parseformula("p")), Ł4) == true
@test hybridalphaprove(⊤, →(α, parseformula("p")), Ł4) == false
@test hybridalphaprove(⊤, →(β, parseformula("p")), Ł4) == false
@test hybridalphaprove(⊤, →(⊤, parseformula("p")), Ł4) == false

@test hybridalphaprove(⊥, →(parseformula("p"), parseformula("p")), Ł4) == true
@test hybridalphaprove(α, →(parseformula("p"), parseformula("p")), Ł4) == true
@test hybridalphaprove(β, →(parseformula("p"), parseformula("p")), Ł4) == true
@test hybridalphaprove(⊤, →(parseformula("p"), parseformula("p")), Ł4) == true

@test hybridalphaprove(⊥, →(parseformula("p"), parseformula("q")), Ł4) == true
@test hybridalphaprove(α, →(parseformula("p"), parseformula("q")), Ł4) == false
@test hybridalphaprove(β, →(parseformula("p"), parseformula("q")), Ł4) == false
@test hybridalphaprove(⊤, →(parseformula("p"), parseformula("q")), Ł4) == false

@test hybridalphaprove(⊥, →(parseformula("q"), parseformula("p")), Ł4) == true
@test hybridalphaprove(α, →(parseformula("q"), parseformula("p")), Ł4) == false
@test hybridalphaprove(β, →(parseformula("q"), parseformula("p")), Ł4) == false
@test hybridalphaprove(⊤, →(parseformula("q"), parseformula("p")), Ł4) == false

############################################################################################
#### H4 ####################################################################################
############################################################################################

using SoleLogics.ManyValuedLogics: H4
using SoleLogics.ManyValuedLogics: α, β

############################################################################################
## Base cases ##############################################################################
############################################################################################

for i ∈ getdomain(H4)
    for j ∈ getdomain(H4)
        @test hybridalphasat(i, j, H4) == hybridalphaprove(i, j, H4)
        for k ∈ getdomain(H4)
            @test hybridalphasat(i, ∨(j,k), H4) == hybridalphaprove(i, ∨(j,k), H4)
            @test hybridalphasat(i, ∧(j,k), H4) == hybridalphaprove(i, ∧(j,k), H4)
            @test hybridalphasat(i, →(j,k), H4) == hybridalphaprove(i, →(j,k), H4)
        end
    end
end

@test hybridalphaprove(⊥, parseformula("p"), H4) == true
@test hybridalphaprove(α, parseformula("p"), H4) == false
@test hybridalphaprove(β, parseformula("p"), H4) == false
@test hybridalphaprove(⊤, parseformula("p"), H4) == false

############################################################################################
## (Strong) disjuction #####################################################################
############################################################################################

@test hybridalphaprove(⊥, ∨(parseformula("p"), ⊥), H4) == true
@test hybridalphaprove(⊥, ∨(parseformula("p"), α), H4) == true
@test hybridalphaprove(⊥, ∨(parseformula("p"), β), H4) == true
@test hybridalphaprove(⊥, ∨(parseformula("p"), ⊤), H4) == true
@test hybridalphaprove(α, ∨(parseformula("p"), ⊥), H4) == false
@test hybridalphaprove(α, ∨(parseformula("p"), α), H4) == true
@test hybridalphaprove(α, ∨(parseformula("p"), β), H4) == false
@test hybridalphaprove(α, ∨(parseformula("p"), ⊤), H4) == true
@test hybridalphaprove(β, ∨(parseformula("p"), ⊥), H4) == false
@test hybridalphaprove(β, ∨(parseformula("p"), α), H4) == false
@test hybridalphaprove(β, ∨(parseformula("p"), β), H4) == true
@test hybridalphaprove(β, ∨(parseformula("p"), ⊤), H4) == true
@test hybridalphaprove(⊤, ∨(parseformula("p"), ⊥), H4) == false
@test hybridalphaprove(⊤, ∨(parseformula("p"), α), H4) == false
@test hybridalphaprove(⊤, ∨(parseformula("p"), β), H4) == false
@test hybridalphaprove(⊤, ∨(parseformula("p"), ⊤), H4) == true

@test hybridalphaprove(⊥, ∨(⊥, parseformula("p")), H4) == true 
@test hybridalphaprove(⊥, ∨(α, parseformula("p")), H4) == true 
@test hybridalphaprove(⊥, ∨(β, parseformula("p")), H4) == true 
@test hybridalphaprove(⊥, ∨(⊤, parseformula("p")), H4) == true 
@test hybridalphaprove(α, ∨(⊥, parseformula("p")), H4) == false
@test hybridalphaprove(α, ∨(α, parseformula("p")), H4) == true 
@test hybridalphaprove(α, ∨(β, parseformula("p")), H4) == false 
@test hybridalphaprove(α, ∨(⊤, parseformula("p")), H4) == true 
@test hybridalphaprove(β, ∨(⊥, parseformula("p")), H4) == false 
@test hybridalphaprove(β, ∨(α, parseformula("p")), H4) == false 
@test hybridalphaprove(β, ∨(β, parseformula("p")), H4) == true 
@test hybridalphaprove(β, ∨(⊤, parseformula("p")), H4) == true 
@test hybridalphaprove(⊤, ∨(⊥, parseformula("p")), H4) == false 
@test hybridalphaprove(⊤, ∨(α, parseformula("p")), H4) == false 
@test hybridalphaprove(⊤, ∨(β, parseformula("p")), H4) == false 
@test hybridalphaprove(⊤, ∨(⊤, parseformula("p")), H4) == true 

@test hybridalphaprove(⊥, ∨(parseformula("p"), parseformula("p")), H4) == true
@test hybridalphaprove(α, ∨(parseformula("p"), parseformula("p")), H4) == false
@test hybridalphaprove(β, ∨(parseformula("p"), parseformula("p")), H4) == false
@test hybridalphaprove(⊤, ∨(parseformula("p"), parseformula("p")), H4) == false

@test hybridalphaprove(⊥, ∨(parseformula("p"), parseformula("q")), H4) == true
@test hybridalphaprove(α, ∨(parseformula("p"), parseformula("q")), H4) == false
@test hybridalphaprove(β, ∨(parseformula("p"), parseformula("q")), H4) == false
@test hybridalphaprove(⊤, ∨(parseformula("p"), parseformula("q")), H4) == false

@test hybridalphaprove(⊥, ∨(parseformula("q"), parseformula("p")), H4) == true
@test hybridalphaprove(α, ∨(parseformula("q"), parseformula("p")), H4) == false
@test hybridalphaprove(β, ∨(parseformula("q"), parseformula("p")), H4) == false
@test hybridalphaprove(⊤, ∨(parseformula("q"), parseformula("p")), H4) == false

############################################################################################
## (Strong) conjunction ####################################################################
############################################################################################

@test hybridalphaprove(⊥, ∧(parseformula("p"), ⊥), H4) == true
@test hybridalphaprove(⊥, ∧(parseformula("p"), α), H4) == true
@test hybridalphaprove(⊥, ∧(parseformula("p"), β), H4) == true
@test hybridalphaprove(⊥, ∧(parseformula("p"), ⊤), H4) == true
@test hybridalphaprove(α, ∧(parseformula("p"), ⊥), H4) == false
@test hybridalphaprove(α, ∧(parseformula("p"), α), H4) == false
@test hybridalphaprove(α, ∧(parseformula("p"), β), H4) == false
@test hybridalphaprove(α, ∧(parseformula("p"), ⊤), H4) == false
@test hybridalphaprove(β, ∧(parseformula("p"), ⊥), H4) == false
@test hybridalphaprove(β, ∧(parseformula("p"), α), H4) == false
@test hybridalphaprove(β, ∧(parseformula("p"), β), H4) == false
@test hybridalphaprove(β, ∧(parseformula("p"), ⊤), H4) == false
@test hybridalphaprove(⊤, ∧(parseformula("p"), ⊥), H4) == false
@test hybridalphaprove(⊤, ∧(parseformula("p"), α), H4) == false
@test hybridalphaprove(⊤, ∧(parseformula("p"), β), H4) == false
@test hybridalphaprove(⊤, ∧(parseformula("p"), ⊤), H4) == false

@test hybridalphaprove(⊥, ∧(⊥, parseformula("p")), H4) == true 
@test hybridalphaprove(⊥, ∧(α, parseformula("p")), H4) == true 
@test hybridalphaprove(⊥, ∧(β, parseformula("p")), H4) == true 
@test hybridalphaprove(⊥, ∧(⊤, parseformula("p")), H4) == true 
@test hybridalphaprove(α, ∧(⊥, parseformula("p")), H4) == false
@test hybridalphaprove(α, ∧(α, parseformula("p")), H4) == false 
@test hybridalphaprove(α, ∧(β, parseformula("p")), H4) == false 
@test hybridalphaprove(α, ∧(⊤, parseformula("p")), H4) == false 
@test hybridalphaprove(β, ∧(⊥, parseformula("p")), H4) == false 
@test hybridalphaprove(β, ∧(α, parseformula("p")), H4) == false 
@test hybridalphaprove(β, ∧(β, parseformula("p")), H4) == false 
@test hybridalphaprove(β, ∧(⊤, parseformula("p")), H4) == false 
@test hybridalphaprove(⊤, ∧(⊥, parseformula("p")), H4) == false 
@test hybridalphaprove(⊤, ∧(α, parseformula("p")), H4) == false 
@test hybridalphaprove(⊤, ∧(β, parseformula("p")), H4) == false 
@test hybridalphaprove(⊤, ∧(⊤, parseformula("p")), H4) == false 

@test hybridalphaprove(⊥, ∧(parseformula("p"), parseformula("p")), H4) == true
@test hybridalphaprove(α, ∧(parseformula("p"), parseformula("p")), H4) == false
@test hybridalphaprove(β, ∧(parseformula("p"), parseformula("p")), H4) == false
@test hybridalphaprove(⊤, ∧(parseformula("p"), parseformula("p")), H4) == false

@test hybridalphaprove(⊥, ∧(parseformula("p"), parseformula("q")), H4) == true
@test hybridalphaprove(α, ∧(parseformula("p"), parseformula("q")), H4) == false
@test hybridalphaprove(β, ∧(parseformula("p"), parseformula("q")), H4) == false
@test hybridalphaprove(⊤, ∧(parseformula("p"), parseformula("q")), H4) == false

@test hybridalphaprove(⊥, ∧(parseformula("q"), parseformula("p")), H4) == true
@test hybridalphaprove(α, ∧(parseformula("q"), parseformula("p")), H4) == false
@test hybridalphaprove(β, ∧(parseformula("q"), parseformula("p")), H4) == false
@test hybridalphaprove(⊤, ∧(parseformula("q"), parseformula("p")), H4) == false

############################################################################################
## Implication #############################################################################
############################################################################################

@test hybridalphaprove(⊥, →(parseformula("p"), ⊥), H4) == true
@test hybridalphaprove(⊥, →(parseformula("p"), α), H4) == true
@test hybridalphaprove(⊥, →(parseformula("p"), β), H4) == true
@test hybridalphaprove(⊥, →(parseformula("p"), ⊤), H4) == true
@test hybridalphaprove(α, →(parseformula("p"), ⊥), H4) == false
@test hybridalphaprove(α, →(parseformula("p"), α), H4) == true
@test hybridalphaprove(α, →(parseformula("p"), β), H4) == false
@test hybridalphaprove(α, →(parseformula("p"), ⊤), H4) == true
@test hybridalphaprove(β, →(parseformula("p"), ⊥), H4) == false
@test hybridalphaprove(β, →(parseformula("p"), α), H4) == false
@test hybridalphaprove(β, →(parseformula("p"), β), H4) == true
@test hybridalphaprove(β, →(parseformula("p"), ⊤), H4) == true
@test hybridalphaprove(⊤, →(parseformula("p"), ⊥), H4) == false
@test hybridalphaprove(⊤, →(parseformula("p"), α), H4) == false
@test hybridalphaprove(⊤, →(parseformula("p"), β), H4) == false
@test hybridalphaprove(⊤, →(parseformula("p"), ⊤), H4) == true

@test hybridalphaprove(⊥, →(⊥, parseformula("p")), H4) == true
@test hybridalphaprove(⊥, →(α, parseformula("p")), H4) == true
@test hybridalphaprove(⊥, →(β, parseformula("p")), H4) == true
@test hybridalphaprove(⊥, →(⊤, parseformula("p")), H4) == true
@test hybridalphaprove(α, →(⊥, parseformula("p")), H4) == true
@test hybridalphaprove(α, →(α, parseformula("p")), H4) == false
@test hybridalphaprove(α, →(β, parseformula("p")), H4) == true
@test hybridalphaprove(α, →(⊤, parseformula("p")), H4) == false
@test hybridalphaprove(β, →(⊥, parseformula("p")), H4) == true
@test hybridalphaprove(β, →(α, parseformula("p")), H4) == true
@test hybridalphaprove(β, →(β, parseformula("p")), H4) == false
@test hybridalphaprove(β, →(⊤, parseformula("p")), H4) == false
@test hybridalphaprove(⊤, →(⊥, parseformula("p")), H4) == true
@test hybridalphaprove(⊤, →(α, parseformula("p")), H4) == false
@test hybridalphaprove(⊤, →(β, parseformula("p")), H4) == false
@test hybridalphaprove(⊤, →(⊤, parseformula("p")), H4) == false

@test hybridalphaprove(⊥, →(parseformula("p"), parseformula("p")), H4) == true
@test hybridalphaprove(α, →(parseformula("p"), parseformula("p")), H4) == true
@test hybridalphaprove(β, →(parseformula("p"), parseformula("p")), H4) == true
@test hybridalphaprove(⊤, →(parseformula("p"), parseformula("p")), H4) == true

@test hybridalphaprove(⊥, →(parseformula("p"), parseformula("q")), H4) == true
@test hybridalphaprove(α, →(parseformula("p"), parseformula("q")), H4) == false
@test hybridalphaprove(β, →(parseformula("p"), parseformula("q")), H4) == false
@test hybridalphaprove(⊤, →(parseformula("p"), parseformula("q")), H4) == false

@test hybridalphaprove(⊥, →(parseformula("q"), parseformula("p")), H4) == true
@test hybridalphaprove(α, →(parseformula("q"), parseformula("p")), H4) == false
@test hybridalphaprove(β, →(parseformula("q"), parseformula("p")), H4) == false
@test hybridalphaprove(⊤, →(parseformula("q"), parseformula("p")), H4) == false
