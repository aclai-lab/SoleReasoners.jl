############################################################################################
#### G4 ####################################################################################
############################################################################################

include("algebras/g4.jl")

############################################################################################
## Base cases ##############################################################################
############################################################################################

for i ∈ getdomain(G4)
    for j ∈ getdomain(G4)
        @test alphasat(i, j, G4) == alphaprove(i, j, G4)
        for k ∈ getdomain(G4)
            @test alphasat(i, ∨(j,k), G4) == alphaprove(i, ∨(j,k), G4)
            @test alphasat(i, ∧(j,k), G4) == alphaprove(i, ∧(j,k), G4)
            @test alphasat(i, →(j,k), G4) == alphaprove(i, →(j,k), G4)
        end
    end
end

@test alphaprove(⊥, parseformula("p"), G4) == true
@test alphaprove(α, parseformula("p"), G4) == false
@test alphaprove(β, parseformula("p"), G4) == false
@test alphaprove(⊤, parseformula("p"), G4) == false

############################################################################################
## (Strong) disjunction ####################################################################
############################################################################################

@test alphaprove(⊥, ∨(parseformula("p"), ⊥), G4) == true
@test alphaprove(⊥, ∨(parseformula("p"), α), G4) == true
@test alphaprove(⊥, ∨(parseformula("p"), β), G4) == true
@test alphaprove(⊥, ∨(parseformula("p"), ⊤), G4) == true
@test alphaprove(α, ∨(parseformula("p"), ⊥), G4) == false
@test alphaprove(α, ∨(parseformula("p"), α), G4) == true
@test alphaprove(α, ∨(parseformula("p"), β), G4) == true
@test alphaprove(α, ∨(parseformula("p"), ⊤), G4) == true
@test alphaprove(β, ∨(parseformula("p"), ⊥), G4) == false
@test alphaprove(β, ∨(parseformula("p"), α), G4) == false
@test alphaprove(β, ∨(parseformula("p"), β), G4) == true
@test alphaprove(β, ∨(parseformula("p"), ⊤), G4) == true
@test alphaprove(⊤, ∨(parseformula("p"), ⊥), G4) == false
@test alphaprove(⊤, ∨(parseformula("p"), α), G4) == false
@test alphaprove(⊤, ∨(parseformula("p"), β), G4) == false
@test alphaprove(⊤, ∨(parseformula("p"), ⊤), G4) == true

@test alphaprove(⊥, ∨(⊥, parseformula("p")), G4) == true
@test alphaprove(⊥, ∨(α, parseformula("p")), G4) == true 
@test alphaprove(⊥, ∨(β, parseformula("p")), G4) == true 
@test alphaprove(⊥, ∨(⊤, parseformula("p")), G4) == true 
@test alphaprove(α, ∨(⊥, parseformula("p")), G4) == false
@test alphaprove(α, ∨(α, parseformula("p")), G4) == true 
@test alphaprove(α, ∨(β, parseformula("p")), G4) == true 
@test alphaprove(α, ∨(⊤, parseformula("p")), G4) == true 
@test alphaprove(β, ∨(⊥, parseformula("p")), G4) == false 
@test alphaprove(β, ∨(α, parseformula("p")), G4) == false 
@test alphaprove(β, ∨(β, parseformula("p")), G4) == true 
@test alphaprove(β, ∨(⊤, parseformula("p")), G4) == true 
@test alphaprove(⊤, ∨(⊥, parseformula("p")), G4) == false 
@test alphaprove(⊤, ∨(α, parseformula("p")), G4) == false 
@test alphaprove(⊤, ∨(β, parseformula("p")), G4) == false 
@test alphaprove(⊤, ∨(⊤, parseformula("p")), G4) == true 

@test alphaprove(⊥, ∨(parseformula("p"), parseformula("p")), G4) == true
@test alphaprove(α, ∨(parseformula("p"), parseformula("p")), G4) == false
@test alphaprove(β, ∨(parseformula("p"), parseformula("p")), G4) == false
@test alphaprove(⊤, ∨(parseformula("p"), parseformula("p")), G4) == false

@test alphaprove(⊥, ∨(parseformula("p"), parseformula("q")), G4) == true
@test alphaprove(α, ∨(parseformula("p"), parseformula("q")), G4) == false
@test alphaprove(β, ∨(parseformula("p"), parseformula("q")), G4) == false
@test alphaprove(⊤, ∨(parseformula("p"), parseformula("q")), G4) == false

@test alphaprove(⊥, ∨(parseformula("q"), parseformula("p")), G4) == true
@test alphaprove(α, ∨(parseformula("q"), parseformula("p")), G4) == false
@test alphaprove(β, ∨(parseformula("q"), parseformula("p")), G4) == false
@test alphaprove(⊤, ∨(parseformula("q"), parseformula("p")), G4) == false

############################################################################################
## (Strong) conjunction ####################################################################
############################################################################################

@test alphaprove(⊥, ∧(parseformula("p"), ⊥), G4) == true
@test alphaprove(⊥, ∧(parseformula("p"), α), G4) == true
@test alphaprove(⊥, ∧(parseformula("p"), β), G4) == true
@test alphaprove(⊥, ∧(parseformula("p"), ⊤), G4) == true
@test alphaprove(α, ∧(parseformula("p"), ⊥), G4) == false
@test alphaprove(α, ∧(parseformula("p"), α), G4) == false
@test alphaprove(α, ∧(parseformula("p"), β), G4) == false
@test alphaprove(α, ∧(parseformula("p"), ⊤), G4) == false
@test alphaprove(β, ∧(parseformula("p"), ⊥), G4) == false
@test alphaprove(β, ∧(parseformula("p"), α), G4) == false
@test alphaprove(β, ∧(parseformula("p"), β), G4) == false
@test alphaprove(β, ∧(parseformula("p"), ⊤), G4) == false
@test alphaprove(⊤, ∧(parseformula("p"), ⊥), G4) == false
@test alphaprove(⊤, ∧(parseformula("p"), α), G4) == false
@test alphaprove(⊤, ∧(parseformula("p"), β), G4) == false
@test alphaprove(⊤, ∧(parseformula("p"), ⊤), G4) == false

@test alphaprove(⊥, ∧(⊥, parseformula("p")), G4) == true 
@test alphaprove(⊥, ∧(α, parseformula("p")), G4) == true 
@test alphaprove(⊥, ∧(β, parseformula("p")), G4) == true 
@test alphaprove(⊥, ∧(⊤, parseformula("p")), G4) == true 
@test alphaprove(α, ∧(⊥, parseformula("p")), G4) == false
@test alphaprove(α, ∧(α, parseformula("p")), G4) == false 
@test alphaprove(α, ∧(β, parseformula("p")), G4) == false 
@test alphaprove(α, ∧(⊤, parseformula("p")), G4) == false 
@test alphaprove(β, ∧(⊥, parseformula("p")), G4) == false 
@test alphaprove(β, ∧(α, parseformula("p")), G4) == false 
@test alphaprove(β, ∧(β, parseformula("p")), G4) == false 
@test alphaprove(β, ∧(⊤, parseformula("p")), G4) == false 
@test alphaprove(⊤, ∧(⊥, parseformula("p")), G4) == false 
@test alphaprove(⊤, ∧(α, parseformula("p")), G4) == false 
@test alphaprove(⊤, ∧(β, parseformula("p")), G4) == false 
@test alphaprove(⊤, ∧(⊤, parseformula("p")), G4) == false 

@test alphaprove(⊥, ∧(parseformula("p"), parseformula("p")), G4) == true
@test alphaprove(α, ∧(parseformula("p"), parseformula("p")), G4) == false
@test alphaprove(β, ∧(parseformula("p"), parseformula("p")), G4) == false
@test alphaprove(⊤, ∧(parseformula("p"), parseformula("p")), G4) == false

@test alphaprove(⊥, ∧(parseformula("p"), parseformula("q")), G4) == true
@test alphaprove(α, ∧(parseformula("p"), parseformula("q")), G4) == false
@test alphaprove(β, ∧(parseformula("p"), parseformula("q")), G4) == false
@test alphaprove(⊤, ∧(parseformula("p"), parseformula("q")), G4) == false

@test alphaprove(⊥, ∧(parseformula("q"), parseformula("p")), G4) == true
@test alphaprove(α, ∧(parseformula("q"), parseformula("p")), G4) == false
@test alphaprove(β, ∧(parseformula("q"), parseformula("p")), G4) == false
@test alphaprove(⊤, ∧(parseformula("q"), parseformula("p")), G4) == false

############################################################################################
## Implication #############################################################################
############################################################################################

@test alphaprove(⊥, →(parseformula("p"), ⊥), G4) == true
@test alphaprove(⊥, →(parseformula("p"), α), G4) == true
@test alphaprove(⊥, →(parseformula("p"), β), G4) == true
@test alphaprove(⊥, →(parseformula("p"), ⊤), G4) == true
@test alphaprove(α, →(parseformula("p"), ⊥), G4) == false
@test alphaprove(α, →(parseformula("p"), α), G4) == true
@test alphaprove(α, →(parseformula("p"), β), G4) == true
@test alphaprove(α, →(parseformula("p"), ⊤), G4) == true
@test alphaprove(β, →(parseformula("p"), ⊥), G4) == false
@test alphaprove(β, →(parseformula("p"), α), G4) == false
@test alphaprove(β, →(parseformula("p"), β), G4) == true
@test alphaprove(β, →(parseformula("p"), ⊤), G4) == true
@test alphaprove(⊤, →(parseformula("p"), ⊥), G4) == false
@test alphaprove(⊤, →(parseformula("p"), α), G4) == false
@test alphaprove(⊤, →(parseformula("p"), β), G4) == false
@test alphaprove(⊤, →(parseformula("p"), ⊤), G4) == true

@test alphaprove(⊥, →(⊥, parseformula("p")), G4) == true
@test alphaprove(⊥, →(α, parseformula("p")), G4) == true
@test alphaprove(⊥, →(β, parseformula("p")), G4) == true
@test alphaprove(⊥, →(⊤, parseformula("p")), G4) == true
@test alphaprove(α, →(⊥, parseformula("p")), G4) == true
@test alphaprove(α, →(α, parseformula("p")), G4) == false
@test alphaprove(α, →(β, parseformula("p")), G4) == false
@test alphaprove(α, →(⊤, parseformula("p")), G4) == false
@test alphaprove(β, →(⊥, parseformula("p")), G4) == true
@test alphaprove(β, →(α, parseformula("p")), G4) == false
@test alphaprove(β, →(β, parseformula("p")), G4) == false
@test alphaprove(β, →(⊤, parseformula("p")), G4) == false
@test alphaprove(⊤, →(⊥, parseformula("p")), G4) == true
@test alphaprove(⊤, →(α, parseformula("p")), G4) == false
@test alphaprove(⊤, →(β, parseformula("p")), G4) == false
@test alphaprove(⊤, →(⊤, parseformula("p")), G4) == false

@test alphaprove(⊥, →(parseformula("p"), parseformula("p")), G4) == true
@test alphaprove(α, →(parseformula("p"), parseformula("p")), G4) == true
@test alphaprove(β, →(parseformula("p"), parseformula("p")), G4) == true
@test alphaprove(⊤, →(parseformula("p"), parseformula("p")), G4) == true

@test alphaprove(⊥, →(parseformula("p"), parseformula("q")), G4) == true
@test alphaprove(α, →(parseformula("p"), parseformula("q")), G4) == false
@test alphaprove(β, →(parseformula("p"), parseformula("q")), G4) == false
@test alphaprove(⊤, →(parseformula("p"), parseformula("q")), G4) == false

@test alphaprove(⊥, →(parseformula("q"), parseformula("p")), G4) == true
@test alphaprove(α, →(parseformula("q"), parseformula("p")), G4) == false
@test alphaprove(β, →(parseformula("q"), parseformula("p")), G4) == false
@test alphaprove(⊤, →(parseformula("q"), parseformula("p")), G4) == false

############################################################################################
#### Ł4 ####################################################################################
############################################################################################

include("algebras/l4.jl")

############################################################################################
## Base cases ##############################################################################
############################################################################################

for i ∈ getdomain(Ł4)
    for j ∈ getdomain(Ł4)
        @test alphasat(i, j, Ł4) == alphaprove(i, j, Ł4)
        for k ∈ getdomain(Ł4)
            @test alphasat(i, ∨(j,k), Ł4) == alphaprove(i, ∨(j,k), Ł4)
            @test alphasat(i, ∧(j,k), Ł4) == alphaprove(i, ∧(j,k), Ł4)
            @test alphasat(i, →(j,k), Ł4) == alphaprove(i, →(j,k), Ł4)
        end
    end
end

@test alphaprove(⊥, parseformula("p"), Ł4) == true
@test alphaprove(α, parseformula("p"), Ł4) == false
@test alphaprove(β, parseformula("p"), Ł4) == false
@test alphaprove(⊤, parseformula("p"), Ł4) == false

############################################################################################
## (Strong) disjunction ####################################################################
############################################################################################

@test alphaprove(⊥, ∨(parseformula("p"), ⊥), Ł4) == true
@test alphaprove(⊥, ∨(parseformula("p"), α), Ł4) == true
@test alphaprove(⊥, ∨(parseformula("p"), β), Ł4) == true
@test alphaprove(⊥, ∨(parseformula("p"), ⊤), Ł4) == true
@test alphaprove(α, ∨(parseformula("p"), ⊥), Ł4) == false
@test alphaprove(α, ∨(parseformula("p"), α), Ł4) == true
@test alphaprove(α, ∨(parseformula("p"), β), Ł4) == true
@test alphaprove(α, ∨(parseformula("p"), ⊤), Ł4) == true
@test alphaprove(β, ∨(parseformula("p"), ⊥), Ł4) == false
@test alphaprove(β, ∨(parseformula("p"), α), Ł4) == false
@test alphaprove(β, ∨(parseformula("p"), β), Ł4) == true
@test alphaprove(β, ∨(parseformula("p"), ⊤), Ł4) == true
@test alphaprove(⊤, ∨(parseformula("p"), ⊥), Ł4) == false
@test alphaprove(⊤, ∨(parseformula("p"), α), Ł4) == false
@test alphaprove(⊤, ∨(parseformula("p"), β), Ł4) == false
@test alphaprove(⊤, ∨(parseformula("p"), ⊤), Ł4) == true

@test alphaprove(⊥, ∨(⊥, parseformula("p")), Ł4) == true
@test alphaprove(⊥, ∨(α, parseformula("p")), Ł4) == true 
@test alphaprove(⊥, ∨(β, parseformula("p")), Ł4) == true 
@test alphaprove(⊥, ∨(⊤, parseformula("p")), Ł4) == true 
@test alphaprove(α, ∨(⊥, parseformula("p")), Ł4) == false
@test alphaprove(α, ∨(α, parseformula("p")), Ł4) == true 
@test alphaprove(α, ∨(β, parseformula("p")), Ł4) == true 
@test alphaprove(α, ∨(⊤, parseformula("p")), Ł4) == true 
@test alphaprove(β, ∨(⊥, parseformula("p")), Ł4) == false 
@test alphaprove(β, ∨(α, parseformula("p")), Ł4) == false 
@test alphaprove(β, ∨(β, parseformula("p")), Ł4) == true 
@test alphaprove(β, ∨(⊤, parseformula("p")), Ł4) == true 
@test alphaprove(⊤, ∨(⊥, parseformula("p")), Ł4) == false 
@test alphaprove(⊤, ∨(α, parseformula("p")), Ł4) == false 
@test alphaprove(⊤, ∨(β, parseformula("p")), Ł4) == false 
@test alphaprove(⊤, ∨(⊤, parseformula("p")), Ł4) == true 

@test alphaprove(⊥, ∨(parseformula("p"), parseformula("p")), Ł4) == true
@test alphaprove(α, ∨(parseformula("p"), parseformula("p")), Ł4) == false
@test alphaprove(β, ∨(parseformula("p"), parseformula("p")), Ł4) == false
@test alphaprove(⊤, ∨(parseformula("p"), parseformula("p")), Ł4) == false

@test alphaprove(⊥, ∨(parseformula("p"), parseformula("q")), Ł4) == true
@test alphaprove(α, ∨(parseformula("p"), parseformula("q")), Ł4) == false
@test alphaprove(β, ∨(parseformula("p"), parseformula("q")), Ł4) == false
@test alphaprove(⊤, ∨(parseformula("p"), parseformula("q")), Ł4) == false

@test alphaprove(⊥, ∨(parseformula("q"), parseformula("p")), Ł4) == true
@test alphaprove(α, ∨(parseformula("q"), parseformula("p")), Ł4) == false
@test alphaprove(β, ∨(parseformula("q"), parseformula("p")), Ł4) == false
@test alphaprove(⊤, ∨(parseformula("q"), parseformula("p")), Ł4) == false

############################################################################################
## (Strong) conjunction ####################################################################
############################################################################################

@test alphaprove(⊥, ∧(parseformula("p"), ⊥), Ł4) == true
@test alphaprove(⊥, ∧(parseformula("p"), α), Ł4) == true
@test alphaprove(⊥, ∧(parseformula("p"), β), Ł4) == true
@test alphaprove(⊥, ∧(parseformula("p"), ⊤), Ł4) == true
@test alphaprove(α, ∧(parseformula("p"), ⊥), Ł4) == false
@test alphaprove(α, ∧(parseformula("p"), α), Ł4) == false
@test alphaprove(α, ∧(parseformula("p"), β), Ł4) == false
@test alphaprove(α, ∧(parseformula("p"), ⊤), Ł4) == false
@test alphaprove(β, ∧(parseformula("p"), ⊥), Ł4) == false
@test alphaprove(β, ∧(parseformula("p"), α), Ł4) == false
@test alphaprove(β, ∧(parseformula("p"), β), Ł4) == false
@test alphaprove(β, ∧(parseformula("p"), ⊤), Ł4) == false
@test alphaprove(⊤, ∧(parseformula("p"), ⊥), Ł4) == false
@test alphaprove(⊤, ∧(parseformula("p"), α), Ł4) == false
@test alphaprove(⊤, ∧(parseformula("p"), β), Ł4) == false
@test alphaprove(⊤, ∧(parseformula("p"), ⊤), Ł4) == false

@test alphaprove(⊥, ∧(⊥, parseformula("p")), Ł4) == true 
@test alphaprove(⊥, ∧(α, parseformula("p")), Ł4) == true 
@test alphaprove(⊥, ∧(β, parseformula("p")), Ł4) == true 
@test alphaprove(⊥, ∧(⊤, parseformula("p")), Ł4) == true 
@test alphaprove(α, ∧(⊥, parseformula("p")), Ł4) == false
@test alphaprove(α, ∧(α, parseformula("p")), Ł4) == false 
@test alphaprove(α, ∧(β, parseformula("p")), Ł4) == false 
@test alphaprove(α, ∧(⊤, parseformula("p")), Ł4) == false 
@test alphaprove(β, ∧(⊥, parseformula("p")), Ł4) == false 
@test alphaprove(β, ∧(α, parseformula("p")), Ł4) == false 
@test alphaprove(β, ∧(β, parseformula("p")), Ł4) == false 
@test alphaprove(β, ∧(⊤, parseformula("p")), Ł4) == false 
@test alphaprove(⊤, ∧(⊥, parseformula("p")), Ł4) == false 
@test alphaprove(⊤, ∧(α, parseformula("p")), Ł4) == false 
@test alphaprove(⊤, ∧(β, parseformula("p")), Ł4) == false 
@test alphaprove(⊤, ∧(⊤, parseformula("p")), Ł4) == false 

@test alphaprove(⊥, ∧(parseformula("p"), parseformula("p")), Ł4) == true
@test alphaprove(α, ∧(parseformula("p"), parseformula("p")), Ł4) == false
@test alphaprove(β, ∧(parseformula("p"), parseformula("p")), Ł4) == false
@test alphaprove(⊤, ∧(parseformula("p"), parseformula("p")), Ł4) == false

@test alphaprove(⊥, ∧(parseformula("p"), parseformula("q")), Ł4) == true
@test alphaprove(α, ∧(parseformula("p"), parseformula("q")), Ł4) == false
@test alphaprove(β, ∧(parseformula("p"), parseformula("q")), Ł4) == false
@test alphaprove(⊤, ∧(parseformula("p"), parseformula("q")), Ł4) == false

@test alphaprove(⊥, ∧(parseformula("q"), parseformula("p")), Ł4) == true
@test alphaprove(α, ∧(parseformula("q"), parseformula("p")), Ł4) == false
@test alphaprove(β, ∧(parseformula("q"), parseformula("p")), Ł4) == false
@test alphaprove(⊤, ∧(parseformula("q"), parseformula("p")), Ł4) == false

############################################################################################
## Implication #############################################################################
############################################################################################

@test alphaprove(⊥, →(parseformula("p"), ⊥), Ł4) == true
@test alphaprove(⊥, →(parseformula("p"), α), Ł4) == true
@test alphaprove(⊥, →(parseformula("p"), β), Ł4) == true
@test alphaprove(⊥, →(parseformula("p"), ⊤), Ł4) == true
@test alphaprove(α, →(parseformula("p"), ⊥), Ł4) == false
@test alphaprove(α, →(parseformula("p"), α), Ł4) == true
@test alphaprove(α, →(parseformula("p"), β), Ł4) == true
@test alphaprove(α, →(parseformula("p"), ⊤), Ł4) == true
@test alphaprove(β, →(parseformula("p"), ⊥), Ł4) == false
@test alphaprove(β, →(parseformula("p"), α), Ł4) == false
@test alphaprove(β, →(parseformula("p"), β), Ł4) == true
@test alphaprove(β, →(parseformula("p"), ⊤), Ł4) == true
@test alphaprove(⊤, →(parseformula("p"), ⊥), Ł4) == false
@test alphaprove(⊤, →(parseformula("p"), α), Ł4) == false
@test alphaprove(⊤, →(parseformula("p"), β), Ł4) == false
@test alphaprove(⊤, →(parseformula("p"), ⊤), Ł4) == true

@test alphaprove(⊥, →(⊥, parseformula("p")), Ł4) == true
@test alphaprove(⊥, →(α, parseformula("p")), Ł4) == true
@test alphaprove(⊥, →(β, parseformula("p")), Ł4) == true
@test alphaprove(⊥, →(⊤, parseformula("p")), Ł4) == true
@test alphaprove(α, →(⊥, parseformula("p")), Ł4) == true
@test alphaprove(α, →(α, parseformula("p")), Ł4) == true
@test alphaprove(α, →(β, parseformula("p")), Ł4) == true
@test alphaprove(α, →(⊤, parseformula("p")), Ł4) == false
@test alphaprove(β, →(⊥, parseformula("p")), Ł4) == true
@test alphaprove(β, →(α, parseformula("p")), Ł4) == true
@test alphaprove(β, →(β, parseformula("p")), Ł4) == false
@test alphaprove(β, →(⊤, parseformula("p")), Ł4) == false
@test alphaprove(⊤, →(⊥, parseformula("p")), Ł4) == true
@test alphaprove(⊤, →(α, parseformula("p")), Ł4) == false
@test alphaprove(⊤, →(β, parseformula("p")), Ł4) == false
@test alphaprove(⊤, →(⊤, parseformula("p")), Ł4) == false

@test alphaprove(⊥, →(parseformula("p"), parseformula("p")), Ł4) == true
@test alphaprove(α, →(parseformula("p"), parseformula("p")), Ł4) == true
@test alphaprove(β, →(parseformula("p"), parseformula("p")), Ł4) == true
@test alphaprove(⊤, →(parseformula("p"), parseformula("p")), Ł4) == true

@test alphaprove(⊥, →(parseformula("p"), parseformula("q")), Ł4) == true
@test alphaprove(α, →(parseformula("p"), parseformula("q")), Ł4) == false
@test alphaprove(β, →(parseformula("p"), parseformula("q")), Ł4) == false
@test alphaprove(⊤, →(parseformula("p"), parseformula("q")), Ł4) == false

@test alphaprove(⊥, →(parseformula("q"), parseformula("p")), Ł4) == true
@test alphaprove(α, →(parseformula("q"), parseformula("p")), Ł4) == false
@test alphaprove(β, →(parseformula("q"), parseformula("p")), Ł4) == false
@test alphaprove(⊤, →(parseformula("q"), parseformula("p")), Ł4) == false

############################################################################################
#### H4 ####################################################################################
############################################################################################

include("algebras/h4.jl")

############################################################################################
## Base cases ##############################################################################
############################################################################################

for i ∈ getdomain(H4)
    for j ∈ getdomain(H4)
        @test alphasat(i, j, H4) == alphaprove(i, j, H4)
        for k ∈ getdomain(H4)
            @test alphasat(i, ∨(j,k), H4) == alphaprove(i, ∨(j,k), H4)
            @test alphasat(i, ∧(j,k), H4) == alphaprove(i, ∧(j,k), H4)
            @test alphasat(i, →(j,k), H4) == alphaprove(i, →(j,k), H4)
        end
    end
end

@test alphaprove(⊥, parseformula("p"), H4) == true
@test alphaprove(α, parseformula("p"), H4) == false
@test alphaprove(β, parseformula("p"), H4) == false
@test alphaprove(⊤, parseformula("p"), H4) == false

############################################################################################
## (Strong) disjuction #####################################################################
############################################################################################

@test alphaprove(⊥, ∨(parseformula("p"), ⊥), H4) == true
@test alphaprove(⊥, ∨(parseformula("p"), α), H4) == true
@test alphaprove(⊥, ∨(parseformula("p"), β), H4) == true
@test alphaprove(⊥, ∨(parseformula("p"), ⊤), H4) == true
@test alphaprove(α, ∨(parseformula("p"), ⊥), H4) == false
@test alphaprove(α, ∨(parseformula("p"), α), H4) == true
@test alphaprove(α, ∨(parseformula("p"), β), H4) == false
@test alphaprove(α, ∨(parseformula("p"), ⊤), H4) == true
@test alphaprove(β, ∨(parseformula("p"), ⊥), H4) == false
@test alphaprove(β, ∨(parseformula("p"), α), H4) == false
@test alphaprove(β, ∨(parseformula("p"), β), H4) == true
@test alphaprove(β, ∨(parseformula("p"), ⊤), H4) == true
@test alphaprove(⊤, ∨(parseformula("p"), ⊥), H4) == false
@test alphaprove(⊤, ∨(parseformula("p"), α), H4) == false
@test alphaprove(⊤, ∨(parseformula("p"), β), H4) == false
@test alphaprove(⊤, ∨(parseformula("p"), ⊤), H4) == true

@test alphaprove(⊥, ∨(⊥, parseformula("p")), H4) == true 
@test alphaprove(⊥, ∨(α, parseformula("p")), H4) == true 
@test alphaprove(⊥, ∨(β, parseformula("p")), H4) == true 
@test alphaprove(⊥, ∨(⊤, parseformula("p")), H4) == true 
@test alphaprove(α, ∨(⊥, parseformula("p")), H4) == false
@test alphaprove(α, ∨(α, parseformula("p")), H4) == true 
@test alphaprove(α, ∨(β, parseformula("p")), H4) == false 
@test alphaprove(α, ∨(⊤, parseformula("p")), H4) == true 
@test alphaprove(β, ∨(⊥, parseformula("p")), H4) == false 
@test alphaprove(β, ∨(α, parseformula("p")), H4) == false 
@test alphaprove(β, ∨(β, parseformula("p")), H4) == true 
@test alphaprove(β, ∨(⊤, parseformula("p")), H4) == true 
@test alphaprove(⊤, ∨(⊥, parseformula("p")), H4) == false 
@test alphaprove(⊤, ∨(α, parseformula("p")), H4) == false 
@test alphaprove(⊤, ∨(β, parseformula("p")), H4) == false 
@test alphaprove(⊤, ∨(⊤, parseformula("p")), H4) == true 

@test alphaprove(⊥, ∨(parseformula("p"), parseformula("p")), H4) == true
@test alphaprove(α, ∨(parseformula("p"), parseformula("p")), H4) == false
@test alphaprove(β, ∨(parseformula("p"), parseformula("p")), H4) == false
@test alphaprove(⊤, ∨(parseformula("p"), parseformula("p")), H4) == false

@test alphaprove(⊥, ∨(parseformula("p"), parseformula("q")), H4) == true
@test alphaprove(α, ∨(parseformula("p"), parseformula("q")), H4) == false
@test alphaprove(β, ∨(parseformula("p"), parseformula("q")), H4) == false
@test alphaprove(⊤, ∨(parseformula("p"), parseformula("q")), H4) == false

@test alphaprove(⊥, ∨(parseformula("q"), parseformula("p")), H4) == true
@test alphaprove(α, ∨(parseformula("q"), parseformula("p")), H4) == false
@test alphaprove(β, ∨(parseformula("q"), parseformula("p")), H4) == false
@test alphaprove(⊤, ∨(parseformula("q"), parseformula("p")), H4) == false

############################################################################################
## (Strong) conjunction ####################################################################
############################################################################################

@test alphaprove(⊥, ∧(parseformula("p"), ⊥), H4) == true
@test alphaprove(⊥, ∧(parseformula("p"), α), H4) == true
@test alphaprove(⊥, ∧(parseformula("p"), β), H4) == true
@test alphaprove(⊥, ∧(parseformula("p"), ⊤), H4) == true
@test alphaprove(α, ∧(parseformula("p"), ⊥), H4) == false
@test alphaprove(α, ∧(parseformula("p"), α), H4) == false
@test alphaprove(α, ∧(parseformula("p"), β), H4) == false
@test alphaprove(α, ∧(parseformula("p"), ⊤), H4) == false
@test alphaprove(β, ∧(parseformula("p"), ⊥), H4) == false
@test alphaprove(β, ∧(parseformula("p"), α), H4) == false
@test alphaprove(β, ∧(parseformula("p"), β), H4) == false
@test alphaprove(β, ∧(parseformula("p"), ⊤), H4) == false
@test alphaprove(⊤, ∧(parseformula("p"), ⊥), H4) == false
@test alphaprove(⊤, ∧(parseformula("p"), α), H4) == false
@test alphaprove(⊤, ∧(parseformula("p"), β), H4) == false
@test alphaprove(⊤, ∧(parseformula("p"), ⊤), H4) == false

@test alphaprove(⊥, ∧(⊥, parseformula("p")), H4) == true 
@test alphaprove(⊥, ∧(α, parseformula("p")), H4) == true 
@test alphaprove(⊥, ∧(β, parseformula("p")), H4) == true 
@test alphaprove(⊥, ∧(⊤, parseformula("p")), H4) == true 
@test alphaprove(α, ∧(⊥, parseformula("p")), H4) == false
@test alphaprove(α, ∧(α, parseformula("p")), H4) == false 
@test alphaprove(α, ∧(β, parseformula("p")), H4) == false 
@test alphaprove(α, ∧(⊤, parseformula("p")), H4) == false 
@test alphaprove(β, ∧(⊥, parseformula("p")), H4) == false 
@test alphaprove(β, ∧(α, parseformula("p")), H4) == false 
@test alphaprove(β, ∧(β, parseformula("p")), H4) == false 
@test alphaprove(β, ∧(⊤, parseformula("p")), H4) == false 
@test alphaprove(⊤, ∧(⊥, parseformula("p")), H4) == false 
@test alphaprove(⊤, ∧(α, parseformula("p")), H4) == false 
@test alphaprove(⊤, ∧(β, parseformula("p")), H4) == false 
@test alphaprove(⊤, ∧(⊤, parseformula("p")), H4) == false 

@test alphaprove(⊥, ∧(parseformula("p"), parseformula("p")), H4) == true
@test alphaprove(α, ∧(parseformula("p"), parseformula("p")), H4) == false
@test alphaprove(β, ∧(parseformula("p"), parseformula("p")), H4) == false
@test alphaprove(⊤, ∧(parseformula("p"), parseformula("p")), H4) == false

@test alphaprove(⊥, ∧(parseformula("p"), parseformula("q")), H4) == true
@test alphaprove(α, ∧(parseformula("p"), parseformula("q")), H4) == false
@test alphaprove(β, ∧(parseformula("p"), parseformula("q")), H4) == false
@test alphaprove(⊤, ∧(parseformula("p"), parseformula("q")), H4) == false

@test alphaprove(⊥, ∧(parseformula("q"), parseformula("p")), H4) == true
@test alphaprove(α, ∧(parseformula("q"), parseformula("p")), H4) == false
@test alphaprove(β, ∧(parseformula("q"), parseformula("p")), H4) == false
@test alphaprove(⊤, ∧(parseformula("q"), parseformula("p")), H4) == false

############################################################################################
## Implication #############################################################################
############################################################################################

@test alphaprove(⊥, →(parseformula("p"), ⊥), H4) == true
@test alphaprove(⊥, →(parseformula("p"), α), H4) == true
@test alphaprove(⊥, →(parseformula("p"), β), H4) == true
@test alphaprove(⊥, →(parseformula("p"), ⊤), H4) == true
@test alphaprove(α, →(parseformula("p"), ⊥), H4) == false
@test alphaprove(α, →(parseformula("p"), α), H4) == true
@test alphaprove(α, →(parseformula("p"), β), H4) == false
@test alphaprove(α, →(parseformula("p"), ⊤), H4) == true
@test alphaprove(β, →(parseformula("p"), ⊥), H4) == false
@test alphaprove(β, →(parseformula("p"), α), H4) == false
@test alphaprove(β, →(parseformula("p"), β), H4) == true
@test alphaprove(β, →(parseformula("p"), ⊤), H4) == true
@test alphaprove(⊤, →(parseformula("p"), ⊥), H4) == false
@test alphaprove(⊤, →(parseformula("p"), α), H4) == false
@test alphaprove(⊤, →(parseformula("p"), β), H4) == false
@test alphaprove(⊤, →(parseformula("p"), ⊤), H4) == true

@test alphaprove(⊥, →(⊥, parseformula("p")), H4) == true
@test alphaprove(⊥, →(α, parseformula("p")), H4) == true
@test alphaprove(⊥, →(β, parseformula("p")), H4) == true
@test alphaprove(⊥, →(⊤, parseformula("p")), H4) == true
@test alphaprove(α, →(⊥, parseformula("p")), H4) == true
@test alphaprove(α, →(α, parseformula("p")), H4) == false
@test alphaprove(α, →(β, parseformula("p")), H4) == true
@test alphaprove(α, →(⊤, parseformula("p")), H4) == false
@test alphaprove(β, →(⊥, parseformula("p")), H4) == true
@test alphaprove(β, →(α, parseformula("p")), H4) == true
@test alphaprove(β, →(β, parseformula("p")), H4) == false
@test alphaprove(β, →(⊤, parseformula("p")), H4) == false
@test alphaprove(⊤, →(⊥, parseformula("p")), H4) == true
@test alphaprove(⊤, →(α, parseformula("p")), H4) == false
@test alphaprove(⊤, →(β, parseformula("p")), H4) == false
@test alphaprove(⊤, →(⊤, parseformula("p")), H4) == false

@test alphaprove(⊥, →(parseformula("p"), parseformula("p")), H4) == true
@test alphaprove(α, →(parseformula("p"), parseformula("p")), H4) == true
@test alphaprove(β, →(parseformula("p"), parseformula("p")), H4) == true
@test alphaprove(⊤, →(parseformula("p"), parseformula("p")), H4) == true

@test alphaprove(⊥, →(parseformula("p"), parseformula("q")), H4) == true
@test alphaprove(α, →(parseformula("p"), parseformula("q")), H4) == false
@test alphaprove(β, →(parseformula("p"), parseformula("q")), H4) == false
@test alphaprove(⊤, →(parseformula("p"), parseformula("q")), H4) == false

@test alphaprove(⊥, →(parseformula("q"), parseformula("p")), H4) == true
@test alphaprove(α, →(parseformula("q"), parseformula("p")), H4) == false
@test alphaprove(β, →(parseformula("q"), parseformula("p")), H4) == false
@test alphaprove(⊤, →(parseformula("q"), parseformula("p")), H4) == false
