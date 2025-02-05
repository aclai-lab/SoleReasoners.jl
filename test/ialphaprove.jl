############################################################################################
#### IG4 ####################################################################################
############################################################################################

using SoleLogics.ManyValuedLogics: G4

IG4 = convert(FiniteIndexFLewAlgebra, G4)

############################################################################################
## Base cases ##############################################################################
############################################################################################

for i ∈ getdomain(IG4)
    for j ∈ getdomain(IG4)
        @test alphasat(i, j, IG4) == alphaprove(i, j, IG4)
        for k ∈ getdomain(IG4)
            @test alphasat(i, ∨(j,k), IG4) == alphaprove(i, ∨(j,k), IG4)
            @test alphasat(i, ∧(j,k), IG4) == alphaprove(i, ∧(j,k), IG4)
            @test alphasat(i, →(j,k), IG4) == alphaprove(i, →(j,k), IG4)
        end
    end
end

@test alphaprove(FiniteIndexTruth(2), parseformula("p"), IG4) == true
@test alphaprove(FiniteIndexTruth(3), parseformula("p"), IG4) == false
@test alphaprove(FiniteIndexTruth(4), parseformula("p"), IG4) == false
@test alphaprove(FiniteIndexTruth(1), parseformula("p"), IG4) == false

############################################################################################
## (Strong) disjunction ####################################################################
############################################################################################

@test alphaprove(FiniteIndexTruth(2), ∨(parseformula("p"), FiniteIndexTruth(2)), IG4) == true
@test alphaprove(FiniteIndexTruth(2), ∨(parseformula("p"), FiniteIndexTruth(3)), IG4) == true
@test alphaprove(FiniteIndexTruth(2), ∨(parseformula("p"), FiniteIndexTruth(4)), IG4) == true
@test alphaprove(FiniteIndexTruth(2), ∨(parseformula("p"), FiniteIndexTruth(1)), IG4) == true
@test alphaprove(FiniteIndexTruth(3), ∨(parseformula("p"), FiniteIndexTruth(2)), IG4) == false
@test alphaprove(FiniteIndexTruth(3), ∨(parseformula("p"), FiniteIndexTruth(3)), IG4) == true
@test alphaprove(FiniteIndexTruth(3), ∨(parseformula("p"), FiniteIndexTruth(4)), IG4) == true
@test alphaprove(FiniteIndexTruth(3), ∨(parseformula("p"), FiniteIndexTruth(1)), IG4) == true
@test alphaprove(FiniteIndexTruth(4), ∨(parseformula("p"), FiniteIndexTruth(2)), IG4) == false
@test alphaprove(FiniteIndexTruth(4), ∨(parseformula("p"), FiniteIndexTruth(3)), IG4) == false
@test alphaprove(FiniteIndexTruth(4), ∨(parseformula("p"), FiniteIndexTruth(4)), IG4) == true
@test alphaprove(FiniteIndexTruth(4), ∨(parseformula("p"), FiniteIndexTruth(1)), IG4) == true
@test alphaprove(FiniteIndexTruth(1), ∨(parseformula("p"), FiniteIndexTruth(2)), IG4) == false
@test alphaprove(FiniteIndexTruth(1), ∨(parseformula("p"), FiniteIndexTruth(3)), IG4) == false
@test alphaprove(FiniteIndexTruth(1), ∨(parseformula("p"), FiniteIndexTruth(4)), IG4) == false
@test alphaprove(FiniteIndexTruth(1), ∨(parseformula("p"), FiniteIndexTruth(1)), IG4) == true

@test alphaprove(FiniteIndexTruth(2), ∨(FiniteIndexTruth(2), parseformula("p")), IG4) == true
@test alphaprove(FiniteIndexTruth(2), ∨(FiniteIndexTruth(3), parseformula("p")), IG4) == true 
@test alphaprove(FiniteIndexTruth(2), ∨(FiniteIndexTruth(4), parseformula("p")), IG4) == true 
@test alphaprove(FiniteIndexTruth(2), ∨(FiniteIndexTruth(1), parseformula("p")), IG4) == true 
@test alphaprove(FiniteIndexTruth(3), ∨(FiniteIndexTruth(2), parseformula("p")), IG4) == false
@test alphaprove(FiniteIndexTruth(3), ∨(FiniteIndexTruth(3), parseformula("p")), IG4) == true 
@test alphaprove(FiniteIndexTruth(3), ∨(FiniteIndexTruth(4), parseformula("p")), IG4) == true 
@test alphaprove(FiniteIndexTruth(3), ∨(FiniteIndexTruth(1), parseformula("p")), IG4) == true 
@test alphaprove(FiniteIndexTruth(4), ∨(FiniteIndexTruth(2), parseformula("p")), IG4) == false 
@test alphaprove(FiniteIndexTruth(4), ∨(FiniteIndexTruth(3), parseformula("p")), IG4) == false 
@test alphaprove(FiniteIndexTruth(4), ∨(FiniteIndexTruth(4), parseformula("p")), IG4) == true 
@test alphaprove(FiniteIndexTruth(4), ∨(FiniteIndexTruth(1), parseformula("p")), IG4) == true 
@test alphaprove(FiniteIndexTruth(1), ∨(FiniteIndexTruth(2), parseformula("p")), IG4) == false 
@test alphaprove(FiniteIndexTruth(1), ∨(FiniteIndexTruth(3), parseformula("p")), IG4) == false 
@test alphaprove(FiniteIndexTruth(1), ∨(FiniteIndexTruth(4), parseformula("p")), IG4) == false 
@test alphaprove(FiniteIndexTruth(1), ∨(FiniteIndexTruth(1), parseformula("p")), IG4) == true 

@test alphaprove(FiniteIndexTruth(2), ∨(parseformula("p"), parseformula("p")), IG4) == true
@test alphaprove(FiniteIndexTruth(3), ∨(parseformula("p"), parseformula("p")), IG4) == false
@test alphaprove(FiniteIndexTruth(4), ∨(parseformula("p"), parseformula("p")), IG4) == false
@test alphaprove(FiniteIndexTruth(1), ∨(parseformula("p"), parseformula("p")), IG4) == false

@test alphaprove(FiniteIndexTruth(2), ∨(parseformula("p"), parseformula("q")), IG4) == true
@test alphaprove(FiniteIndexTruth(3), ∨(parseformula("p"), parseformula("q")), IG4) == false
@test alphaprove(FiniteIndexTruth(4), ∨(parseformula("p"), parseformula("q")), IG4) == false
@test alphaprove(FiniteIndexTruth(1), ∨(parseformula("p"), parseformula("q")), IG4) == false

@test alphaprove(FiniteIndexTruth(2), ∨(parseformula("q"), parseformula("p")), IG4) == true
@test alphaprove(FiniteIndexTruth(3), ∨(parseformula("q"), parseformula("p")), IG4) == false
@test alphaprove(FiniteIndexTruth(4), ∨(parseformula("q"), parseformula("p")), IG4) == false
@test alphaprove(FiniteIndexTruth(1), ∨(parseformula("q"), parseformula("p")), IG4) == false

############################################################################################
## (Strong) conjunction ####################################################################
############################################################################################

@test alphaprove(FiniteIndexTruth(2), ∧(parseformula("p"), FiniteIndexTruth(2)), IG4) == true
@test alphaprove(FiniteIndexTruth(2), ∧(parseformula("p"), FiniteIndexTruth(3)), IG4) == true
@test alphaprove(FiniteIndexTruth(2), ∧(parseformula("p"), FiniteIndexTruth(4)), IG4) == true
@test alphaprove(FiniteIndexTruth(2), ∧(parseformula("p"), FiniteIndexTruth(1)), IG4) == true
@test alphaprove(FiniteIndexTruth(3), ∧(parseformula("p"), FiniteIndexTruth(2)), IG4) == false
@test alphaprove(FiniteIndexTruth(3), ∧(parseformula("p"), FiniteIndexTruth(3)), IG4) == false
@test alphaprove(FiniteIndexTruth(3), ∧(parseformula("p"), FiniteIndexTruth(4)), IG4) == false
@test alphaprove(FiniteIndexTruth(3), ∧(parseformula("p"), FiniteIndexTruth(1)), IG4) == false
@test alphaprove(FiniteIndexTruth(4), ∧(parseformula("p"), FiniteIndexTruth(2)), IG4) == false
@test alphaprove(FiniteIndexTruth(4), ∧(parseformula("p"), FiniteIndexTruth(3)), IG4) == false
@test alphaprove(FiniteIndexTruth(4), ∧(parseformula("p"), FiniteIndexTruth(4)), IG4) == false
@test alphaprove(FiniteIndexTruth(4), ∧(parseformula("p"), FiniteIndexTruth(1)), IG4) == false
@test alphaprove(FiniteIndexTruth(1), ∧(parseformula("p"), FiniteIndexTruth(2)), IG4) == false
@test alphaprove(FiniteIndexTruth(1), ∧(parseformula("p"), FiniteIndexTruth(3)), IG4) == false
@test alphaprove(FiniteIndexTruth(1), ∧(parseformula("p"), FiniteIndexTruth(4)), IG4) == false
@test alphaprove(FiniteIndexTruth(1), ∧(parseformula("p"), FiniteIndexTruth(1)), IG4) == false

@test alphaprove(FiniteIndexTruth(2), ∧(FiniteIndexTruth(2), parseformula("p")), IG4) == true 
@test alphaprove(FiniteIndexTruth(2), ∧(FiniteIndexTruth(3), parseformula("p")), IG4) == true 
@test alphaprove(FiniteIndexTruth(2), ∧(FiniteIndexTruth(4), parseformula("p")), IG4) == true 
@test alphaprove(FiniteIndexTruth(2), ∧(FiniteIndexTruth(1), parseformula("p")), IG4) == true 
@test alphaprove(FiniteIndexTruth(3), ∧(FiniteIndexTruth(2), parseformula("p")), IG4) == false
@test alphaprove(FiniteIndexTruth(3), ∧(FiniteIndexTruth(3), parseformula("p")), IG4) == false 
@test alphaprove(FiniteIndexTruth(3), ∧(FiniteIndexTruth(4), parseformula("p")), IG4) == false 
@test alphaprove(FiniteIndexTruth(3), ∧(FiniteIndexTruth(1), parseformula("p")), IG4) == false 
@test alphaprove(FiniteIndexTruth(4), ∧(FiniteIndexTruth(2), parseformula("p")), IG4) == false 
@test alphaprove(FiniteIndexTruth(4), ∧(FiniteIndexTruth(3), parseformula("p")), IG4) == false 
@test alphaprove(FiniteIndexTruth(4), ∧(FiniteIndexTruth(4), parseformula("p")), IG4) == false 
@test alphaprove(FiniteIndexTruth(4), ∧(FiniteIndexTruth(1), parseformula("p")), IG4) == false 
@test alphaprove(FiniteIndexTruth(1), ∧(FiniteIndexTruth(2), parseformula("p")), IG4) == false 
@test alphaprove(FiniteIndexTruth(1), ∧(FiniteIndexTruth(3), parseformula("p")), IG4) == false 
@test alphaprove(FiniteIndexTruth(1), ∧(FiniteIndexTruth(4), parseformula("p")), IG4) == false 
@test alphaprove(FiniteIndexTruth(1), ∧(FiniteIndexTruth(1), parseformula("p")), IG4) == false 

@test alphaprove(FiniteIndexTruth(2), ∧(parseformula("p"), parseformula("p")), IG4) == true
@test alphaprove(FiniteIndexTruth(3), ∧(parseformula("p"), parseformula("p")), IG4) == false
@test alphaprove(FiniteIndexTruth(4), ∧(parseformula("p"), parseformula("p")), IG4) == false
@test alphaprove(FiniteIndexTruth(1), ∧(parseformula("p"), parseformula("p")), IG4) == false

@test alphaprove(FiniteIndexTruth(2), ∧(parseformula("p"), parseformula("q")), IG4) == true
@test alphaprove(FiniteIndexTruth(3), ∧(parseformula("p"), parseformula("q")), IG4) == false
@test alphaprove(FiniteIndexTruth(4), ∧(parseformula("p"), parseformula("q")), IG4) == false
@test alphaprove(FiniteIndexTruth(1), ∧(parseformula("p"), parseformula("q")), IG4) == false

@test alphaprove(FiniteIndexTruth(2), ∧(parseformula("q"), parseformula("p")), IG4) == true
@test alphaprove(FiniteIndexTruth(3), ∧(parseformula("q"), parseformula("p")), IG4) == false
@test alphaprove(FiniteIndexTruth(4), ∧(parseformula("q"), parseformula("p")), IG4) == false
@test alphaprove(FiniteIndexTruth(1), ∧(parseformula("q"), parseformula("p")), IG4) == false

############################################################################################
## Implication #############################################################################
############################################################################################

@test alphaprove(FiniteIndexTruth(2), →(parseformula("p"), FiniteIndexTruth(2)), IG4) == true
@test alphaprove(FiniteIndexTruth(2), →(parseformula("p"), FiniteIndexTruth(3)), IG4) == true
@test alphaprove(FiniteIndexTruth(2), →(parseformula("p"), FiniteIndexTruth(4)), IG4) == true
@test alphaprove(FiniteIndexTruth(2), →(parseformula("p"), FiniteIndexTruth(1)), IG4) == true
@test alphaprove(FiniteIndexTruth(3), →(parseformula("p"), FiniteIndexTruth(2)), IG4) == false
@test alphaprove(FiniteIndexTruth(3), →(parseformula("p"), FiniteIndexTruth(3)), IG4) == true
@test alphaprove(FiniteIndexTruth(3), →(parseformula("p"), FiniteIndexTruth(4)), IG4) == true
@test alphaprove(FiniteIndexTruth(3), →(parseformula("p"), FiniteIndexTruth(1)), IG4) == true
@test alphaprove(FiniteIndexTruth(4), →(parseformula("p"), FiniteIndexTruth(2)), IG4) == false
@test alphaprove(FiniteIndexTruth(4), →(parseformula("p"), FiniteIndexTruth(3)), IG4) == false
@test alphaprove(FiniteIndexTruth(4), →(parseformula("p"), FiniteIndexTruth(4)), IG4) == true
@test alphaprove(FiniteIndexTruth(4), →(parseformula("p"), FiniteIndexTruth(1)), IG4) == true
@test alphaprove(FiniteIndexTruth(1), →(parseformula("p"), FiniteIndexTruth(2)), IG4) == false
@test alphaprove(FiniteIndexTruth(1), →(parseformula("p"), FiniteIndexTruth(3)), IG4) == false
@test alphaprove(FiniteIndexTruth(1), →(parseformula("p"), FiniteIndexTruth(4)), IG4) == false
@test alphaprove(FiniteIndexTruth(1), →(parseformula("p"), FiniteIndexTruth(1)), IG4) == true

@test alphaprove(FiniteIndexTruth(2), →(FiniteIndexTruth(2), parseformula("p")), IG4) == true
@test alphaprove(FiniteIndexTruth(2), →(FiniteIndexTruth(3), parseformula("p")), IG4) == true
@test alphaprove(FiniteIndexTruth(2), →(FiniteIndexTruth(4), parseformula("p")), IG4) == true
@test alphaprove(FiniteIndexTruth(2), →(FiniteIndexTruth(1), parseformula("p")), IG4) == true
@test alphaprove(FiniteIndexTruth(3), →(FiniteIndexTruth(2), parseformula("p")), IG4) == true
@test alphaprove(FiniteIndexTruth(3), →(FiniteIndexTruth(3), parseformula("p")), IG4) == false
@test alphaprove(FiniteIndexTruth(3), →(FiniteIndexTruth(4), parseformula("p")), IG4) == false
@test alphaprove(FiniteIndexTruth(3), →(FiniteIndexTruth(1), parseformula("p")), IG4) == false
@test alphaprove(FiniteIndexTruth(4), →(FiniteIndexTruth(2), parseformula("p")), IG4) == true
@test alphaprove(FiniteIndexTruth(4), →(FiniteIndexTruth(3), parseformula("p")), IG4) == false
@test alphaprove(FiniteIndexTruth(4), →(FiniteIndexTruth(4), parseformula("p")), IG4) == false
@test alphaprove(FiniteIndexTruth(4), →(FiniteIndexTruth(1), parseformula("p")), IG4) == false
@test alphaprove(FiniteIndexTruth(1), →(FiniteIndexTruth(2), parseformula("p")), IG4) == true
@test alphaprove(FiniteIndexTruth(1), →(FiniteIndexTruth(3), parseformula("p")), IG4) == false
@test alphaprove(FiniteIndexTruth(1), →(FiniteIndexTruth(4), parseformula("p")), IG4) == false
@test alphaprove(FiniteIndexTruth(1), →(FiniteIndexTruth(1), parseformula("p")), IG4) == false

@test alphaprove(FiniteIndexTruth(2), →(parseformula("p"), parseformula("p")), IG4) == true
@test alphaprove(FiniteIndexTruth(3), →(parseformula("p"), parseformula("p")), IG4) == true
@test alphaprove(FiniteIndexTruth(4), →(parseformula("p"), parseformula("p")), IG4) == true
@test alphaprove(FiniteIndexTruth(1), →(parseformula("p"), parseformula("p")), IG4) == true

@test alphaprove(FiniteIndexTruth(2), →(parseformula("p"), parseformula("q")), IG4) == true
@test alphaprove(FiniteIndexTruth(3), →(parseformula("p"), parseformula("q")), IG4) == false
@test alphaprove(FiniteIndexTruth(4), →(parseformula("p"), parseformula("q")), IG4) == false
@test alphaprove(FiniteIndexTruth(1), →(parseformula("p"), parseformula("q")), IG4) == false

@test alphaprove(FiniteIndexTruth(2), →(parseformula("q"), parseformula("p")), IG4) == true
@test alphaprove(FiniteIndexTruth(3), →(parseformula("q"), parseformula("p")), IG4) == false
@test alphaprove(FiniteIndexTruth(4), →(parseformula("q"), parseformula("p")), IG4) == false
@test alphaprove(FiniteIndexTruth(1), →(parseformula("q"), parseformula("p")), IG4) == false

############################################################################################
#### IŁ4 ####################################################################################
############################################################################################

using SoleLogics.ManyValuedLogics: Ł4

IŁ4 = convert(FiniteIndexFLewAlgebra, Ł4)

############################################################################################
## Base cases ##############################################################################
############################################################################################

for i ∈ getdomain(IŁ4)
    for j ∈ getdomain(IŁ4)
        @test alphasat(i, j, IŁ4) == alphaprove(i, j, IŁ4)
        for k ∈ getdomain(IŁ4)
            @test alphasat(i, ∨(j,k), IŁ4) == alphaprove(i, ∨(j,k), IŁ4)
            @test alphasat(i, ∧(j,k), IŁ4) == alphaprove(i, ∧(j,k), IŁ4)
            @test alphasat(i, →(j,k), IŁ4) == alphaprove(i, →(j,k), IŁ4)
        end
    end
end

@test alphaprove(FiniteIndexTruth(2), parseformula("p"), IŁ4) == true
@test alphaprove(FiniteIndexTruth(3), parseformula("p"), IŁ4) == false
@test alphaprove(FiniteIndexTruth(4), parseformula("p"), IŁ4) == false
@test alphaprove(FiniteIndexTruth(1), parseformula("p"), IŁ4) == false

############################################################################################
## (Strong) disjunction ####################################################################
############################################################################################

@test alphaprove(FiniteIndexTruth(2), ∨(parseformula("p"), FiniteIndexTruth(2)), IŁ4) == true
@test alphaprove(FiniteIndexTruth(2), ∨(parseformula("p"), FiniteIndexTruth(3)), IŁ4) == true
@test alphaprove(FiniteIndexTruth(2), ∨(parseformula("p"), FiniteIndexTruth(4)), IŁ4) == true
@test alphaprove(FiniteIndexTruth(2), ∨(parseformula("p"), FiniteIndexTruth(1)), IŁ4) == true
@test alphaprove(FiniteIndexTruth(3), ∨(parseformula("p"), FiniteIndexTruth(2)), IŁ4) == false
@test alphaprove(FiniteIndexTruth(3), ∨(parseformula("p"), FiniteIndexTruth(3)), IŁ4) == true
@test alphaprove(FiniteIndexTruth(3), ∨(parseformula("p"), FiniteIndexTruth(4)), IŁ4) == true
@test alphaprove(FiniteIndexTruth(3), ∨(parseformula("p"), FiniteIndexTruth(1)), IŁ4) == true
@test alphaprove(FiniteIndexTruth(4), ∨(parseformula("p"), FiniteIndexTruth(2)), IŁ4) == false
@test alphaprove(FiniteIndexTruth(4), ∨(parseformula("p"), FiniteIndexTruth(3)), IŁ4) == false
@test alphaprove(FiniteIndexTruth(4), ∨(parseformula("p"), FiniteIndexTruth(4)), IŁ4) == true
@test alphaprove(FiniteIndexTruth(4), ∨(parseformula("p"), FiniteIndexTruth(1)), IŁ4) == true
@test alphaprove(FiniteIndexTruth(1), ∨(parseformula("p"), FiniteIndexTruth(2)), IŁ4) == false
@test alphaprove(FiniteIndexTruth(1), ∨(parseformula("p"), FiniteIndexTruth(3)), IŁ4) == false
@test alphaprove(FiniteIndexTruth(1), ∨(parseformula("p"), FiniteIndexTruth(4)), IŁ4) == false
@test alphaprove(FiniteIndexTruth(1), ∨(parseformula("p"), FiniteIndexTruth(1)), IŁ4) == true

@test alphaprove(FiniteIndexTruth(2), ∨(FiniteIndexTruth(2), parseformula("p")), IŁ4) == true
@test alphaprove(FiniteIndexTruth(2), ∨(FiniteIndexTruth(3), parseformula("p")), IŁ4) == true 
@test alphaprove(FiniteIndexTruth(2), ∨(FiniteIndexTruth(4), parseformula("p")), IŁ4) == true 
@test alphaprove(FiniteIndexTruth(2), ∨(FiniteIndexTruth(1), parseformula("p")), IŁ4) == true 
@test alphaprove(FiniteIndexTruth(3), ∨(FiniteIndexTruth(2), parseformula("p")), IŁ4) == false
@test alphaprove(FiniteIndexTruth(3), ∨(FiniteIndexTruth(3), parseformula("p")), IŁ4) == true 
@test alphaprove(FiniteIndexTruth(3), ∨(FiniteIndexTruth(4), parseformula("p")), IŁ4) == true 
@test alphaprove(FiniteIndexTruth(3), ∨(FiniteIndexTruth(1), parseformula("p")), IŁ4) == true 
@test alphaprove(FiniteIndexTruth(4), ∨(FiniteIndexTruth(2), parseformula("p")), IŁ4) == false 
@test alphaprove(FiniteIndexTruth(4), ∨(FiniteIndexTruth(3), parseformula("p")), IŁ4) == false 
@test alphaprove(FiniteIndexTruth(4), ∨(FiniteIndexTruth(4), parseformula("p")), IŁ4) == true 
@test alphaprove(FiniteIndexTruth(4), ∨(FiniteIndexTruth(1), parseformula("p")), IŁ4) == true 
@test alphaprove(FiniteIndexTruth(1), ∨(FiniteIndexTruth(2), parseformula("p")), IŁ4) == false 
@test alphaprove(FiniteIndexTruth(1), ∨(FiniteIndexTruth(3), parseformula("p")), IŁ4) == false 
@test alphaprove(FiniteIndexTruth(1), ∨(FiniteIndexTruth(4), parseformula("p")), IŁ4) == false 
@test alphaprove(FiniteIndexTruth(1), ∨(FiniteIndexTruth(1), parseformula("p")), IŁ4) == true 

@test alphaprove(FiniteIndexTruth(2), ∨(parseformula("p"), parseformula("p")), IŁ4) == true
@test alphaprove(FiniteIndexTruth(3), ∨(parseformula("p"), parseformula("p")), IŁ4) == false
@test alphaprove(FiniteIndexTruth(4), ∨(parseformula("p"), parseformula("p")), IŁ4) == false
@test alphaprove(FiniteIndexTruth(1), ∨(parseformula("p"), parseformula("p")), IŁ4) == false

@test alphaprove(FiniteIndexTruth(2), ∨(parseformula("p"), parseformula("q")), IŁ4) == true
@test alphaprove(FiniteIndexTruth(3), ∨(parseformula("p"), parseformula("q")), IŁ4) == false
@test alphaprove(FiniteIndexTruth(4), ∨(parseformula("p"), parseformula("q")), IŁ4) == false
@test alphaprove(FiniteIndexTruth(1), ∨(parseformula("p"), parseformula("q")), IŁ4) == false

@test alphaprove(FiniteIndexTruth(2), ∨(parseformula("q"), parseformula("p")), IŁ4) == true
@test alphaprove(FiniteIndexTruth(3), ∨(parseformula("q"), parseformula("p")), IŁ4) == false
@test alphaprove(FiniteIndexTruth(4), ∨(parseformula("q"), parseformula("p")), IŁ4) == false
@test alphaprove(FiniteIndexTruth(1), ∨(parseformula("q"), parseformula("p")), IŁ4) == false

############################################################################################
## (Strong) conjunction ####################################################################
############################################################################################

@test alphaprove(FiniteIndexTruth(2), ∧(parseformula("p"), FiniteIndexTruth(2)), IŁ4) == true
@test alphaprove(FiniteIndexTruth(2), ∧(parseformula("p"), FiniteIndexTruth(3)), IŁ4) == true
@test alphaprove(FiniteIndexTruth(2), ∧(parseformula("p"), FiniteIndexTruth(4)), IŁ4) == true
@test alphaprove(FiniteIndexTruth(2), ∧(parseformula("p"), FiniteIndexTruth(1)), IŁ4) == true
@test alphaprove(FiniteIndexTruth(3), ∧(parseformula("p"), FiniteIndexTruth(2)), IŁ4) == false
@test alphaprove(FiniteIndexTruth(3), ∧(parseformula("p"), FiniteIndexTruth(3)), IŁ4) == false
@test alphaprove(FiniteIndexTruth(3), ∧(parseformula("p"), FiniteIndexTruth(4)), IŁ4) == false
@test alphaprove(FiniteIndexTruth(3), ∧(parseformula("p"), FiniteIndexTruth(1)), IŁ4) == false
@test alphaprove(FiniteIndexTruth(4), ∧(parseformula("p"), FiniteIndexTruth(2)), IŁ4) == false
@test alphaprove(FiniteIndexTruth(4), ∧(parseformula("p"), FiniteIndexTruth(3)), IŁ4) == false
@test alphaprove(FiniteIndexTruth(4), ∧(parseformula("p"), FiniteIndexTruth(4)), IŁ4) == false
@test alphaprove(FiniteIndexTruth(4), ∧(parseformula("p"), FiniteIndexTruth(1)), IŁ4) == false
@test alphaprove(FiniteIndexTruth(1), ∧(parseformula("p"), FiniteIndexTruth(2)), IŁ4) == false
@test alphaprove(FiniteIndexTruth(1), ∧(parseformula("p"), FiniteIndexTruth(3)), IŁ4) == false
@test alphaprove(FiniteIndexTruth(1), ∧(parseformula("p"), FiniteIndexTruth(4)), IŁ4) == false
@test alphaprove(FiniteIndexTruth(1), ∧(parseformula("p"), FiniteIndexTruth(1)), IŁ4) == false

@test alphaprove(FiniteIndexTruth(2), ∧(FiniteIndexTruth(2), parseformula("p")), IŁ4) == true 
@test alphaprove(FiniteIndexTruth(2), ∧(FiniteIndexTruth(3), parseformula("p")), IŁ4) == true 
@test alphaprove(FiniteIndexTruth(2), ∧(FiniteIndexTruth(4), parseformula("p")), IŁ4) == true 
@test alphaprove(FiniteIndexTruth(2), ∧(FiniteIndexTruth(1), parseformula("p")), IŁ4) == true 
@test alphaprove(FiniteIndexTruth(3), ∧(FiniteIndexTruth(2), parseformula("p")), IŁ4) == false
@test alphaprove(FiniteIndexTruth(3), ∧(FiniteIndexTruth(3), parseformula("p")), IŁ4) == false 
@test alphaprove(FiniteIndexTruth(3), ∧(FiniteIndexTruth(4), parseformula("p")), IŁ4) == false 
@test alphaprove(FiniteIndexTruth(3), ∧(FiniteIndexTruth(1), parseformula("p")), IŁ4) == false 
@test alphaprove(FiniteIndexTruth(4), ∧(FiniteIndexTruth(2), parseformula("p")), IŁ4) == false 
@test alphaprove(FiniteIndexTruth(4), ∧(FiniteIndexTruth(3), parseformula("p")), IŁ4) == false 
@test alphaprove(FiniteIndexTruth(4), ∧(FiniteIndexTruth(4), parseformula("p")), IŁ4) == false 
@test alphaprove(FiniteIndexTruth(4), ∧(FiniteIndexTruth(1), parseformula("p")), IŁ4) == false 
@test alphaprove(FiniteIndexTruth(1), ∧(FiniteIndexTruth(2), parseformula("p")), IŁ4) == false 
@test alphaprove(FiniteIndexTruth(1), ∧(FiniteIndexTruth(3), parseformula("p")), IŁ4) == false 
@test alphaprove(FiniteIndexTruth(1), ∧(FiniteIndexTruth(4), parseformula("p")), IŁ4) == false 
@test alphaprove(FiniteIndexTruth(1), ∧(FiniteIndexTruth(1), parseformula("p")), IŁ4) == false 

@test alphaprove(FiniteIndexTruth(2), ∧(parseformula("p"), parseformula("p")), IŁ4) == true
@test alphaprove(FiniteIndexTruth(3), ∧(parseformula("p"), parseformula("p")), IŁ4) == false
@test alphaprove(FiniteIndexTruth(4), ∧(parseformula("p"), parseformula("p")), IŁ4) == false
@test alphaprove(FiniteIndexTruth(1), ∧(parseformula("p"), parseformula("p")), IŁ4) == false

@test alphaprove(FiniteIndexTruth(2), ∧(parseformula("p"), parseformula("q")), IŁ4) == true
@test alphaprove(FiniteIndexTruth(3), ∧(parseformula("p"), parseformula("q")), IŁ4) == false
@test alphaprove(FiniteIndexTruth(4), ∧(parseformula("p"), parseformula("q")), IŁ4) == false
@test alphaprove(FiniteIndexTruth(1), ∧(parseformula("p"), parseformula("q")), IŁ4) == false

@test alphaprove(FiniteIndexTruth(2), ∧(parseformula("q"), parseformula("p")), IŁ4) == true
@test alphaprove(FiniteIndexTruth(3), ∧(parseformula("q"), parseformula("p")), IŁ4) == false
@test alphaprove(FiniteIndexTruth(4), ∧(parseformula("q"), parseformula("p")), IŁ4) == false
@test alphaprove(FiniteIndexTruth(1), ∧(parseformula("q"), parseformula("p")), IŁ4) == false

############################################################################################
## Implication #############################################################################
############################################################################################

@test alphaprove(FiniteIndexTruth(2), →(parseformula("p"), FiniteIndexTruth(2)), IŁ4) == true
@test alphaprove(FiniteIndexTruth(2), →(parseformula("p"), FiniteIndexTruth(3)), IŁ4) == true
@test alphaprove(FiniteIndexTruth(2), →(parseformula("p"), FiniteIndexTruth(4)), IŁ4) == true
@test alphaprove(FiniteIndexTruth(2), →(parseformula("p"), FiniteIndexTruth(1)), IŁ4) == true
@test alphaprove(FiniteIndexTruth(3), →(parseformula("p"), FiniteIndexTruth(2)), IŁ4) == false
@test alphaprove(FiniteIndexTruth(3), →(parseformula("p"), FiniteIndexTruth(3)), IŁ4) == true
@test alphaprove(FiniteIndexTruth(3), →(parseformula("p"), FiniteIndexTruth(4)), IŁ4) == true
@test alphaprove(FiniteIndexTruth(3), →(parseformula("p"), FiniteIndexTruth(1)), IŁ4) == true
@test alphaprove(FiniteIndexTruth(4), →(parseformula("p"), FiniteIndexTruth(2)), IŁ4) == false
@test alphaprove(FiniteIndexTruth(4), →(parseformula("p"), FiniteIndexTruth(3)), IŁ4) == false
@test alphaprove(FiniteIndexTruth(4), →(parseformula("p"), FiniteIndexTruth(4)), IŁ4) == true
@test alphaprove(FiniteIndexTruth(4), →(parseformula("p"), FiniteIndexTruth(1)), IŁ4) == true
@test alphaprove(FiniteIndexTruth(1), →(parseformula("p"), FiniteIndexTruth(2)), IŁ4) == false
@test alphaprove(FiniteIndexTruth(1), →(parseformula("p"), FiniteIndexTruth(3)), IŁ4) == false
@test alphaprove(FiniteIndexTruth(1), →(parseformula("p"), FiniteIndexTruth(4)), IŁ4) == false
@test alphaprove(FiniteIndexTruth(1), →(parseformula("p"), FiniteIndexTruth(1)), IŁ4) == true

@test alphaprove(FiniteIndexTruth(2), →(FiniteIndexTruth(2), parseformula("p")), IŁ4) == true
@test alphaprove(FiniteIndexTruth(2), →(FiniteIndexTruth(3), parseformula("p")), IŁ4) == true
@test alphaprove(FiniteIndexTruth(2), →(FiniteIndexTruth(4), parseformula("p")), IŁ4) == true
@test alphaprove(FiniteIndexTruth(2), →(FiniteIndexTruth(1), parseformula("p")), IŁ4) == true
@test alphaprove(FiniteIndexTruth(3), →(FiniteIndexTruth(2), parseformula("p")), IŁ4) == true
@test alphaprove(FiniteIndexTruth(3), →(FiniteIndexTruth(3), parseformula("p")), IŁ4) == true
@test alphaprove(FiniteIndexTruth(3), →(FiniteIndexTruth(4), parseformula("p")), IŁ4) == true
@test alphaprove(FiniteIndexTruth(3), →(FiniteIndexTruth(1), parseformula("p")), IŁ4) == false
@test alphaprove(FiniteIndexTruth(4), →(FiniteIndexTruth(2), parseformula("p")), IŁ4) == true
@test alphaprove(FiniteIndexTruth(4), →(FiniteIndexTruth(3), parseformula("p")), IŁ4) == true
@test alphaprove(FiniteIndexTruth(4), →(FiniteIndexTruth(4), parseformula("p")), IŁ4) == false
@test alphaprove(FiniteIndexTruth(4), →(FiniteIndexTruth(1), parseformula("p")), IŁ4) == false
@test alphaprove(FiniteIndexTruth(1), →(FiniteIndexTruth(2), parseformula("p")), IŁ4) == true
@test alphaprove(FiniteIndexTruth(1), →(FiniteIndexTruth(3), parseformula("p")), IŁ4) == false
@test alphaprove(FiniteIndexTruth(1), →(FiniteIndexTruth(4), parseformula("p")), IŁ4) == false
@test alphaprove(FiniteIndexTruth(1), →(FiniteIndexTruth(1), parseformula("p")), IŁ4) == false

@test alphaprove(FiniteIndexTruth(2), →(parseformula("p"), parseformula("p")), IŁ4) == true
@test alphaprove(FiniteIndexTruth(3), →(parseformula("p"), parseformula("p")), IŁ4) == true
@test alphaprove(FiniteIndexTruth(4), →(parseformula("p"), parseformula("p")), IŁ4) == true
@test alphaprove(FiniteIndexTruth(1), →(parseformula("p"), parseformula("p")), IŁ4) == true

@test alphaprove(FiniteIndexTruth(2), →(parseformula("p"), parseformula("q")), IŁ4) == true
@test alphaprove(FiniteIndexTruth(3), →(parseformula("p"), parseformula("q")), IŁ4) == false
@test alphaprove(FiniteIndexTruth(4), →(parseformula("p"), parseformula("q")), IŁ4) == false
@test alphaprove(FiniteIndexTruth(1), →(parseformula("p"), parseformula("q")), IŁ4) == false

@test alphaprove(FiniteIndexTruth(2), →(parseformula("q"), parseformula("p")), IŁ4) == true
@test alphaprove(FiniteIndexTruth(3), →(parseformula("q"), parseformula("p")), IŁ4) == false
@test alphaprove(FiniteIndexTruth(4), →(parseformula("q"), parseformula("p")), IŁ4) == false
@test alphaprove(FiniteIndexTruth(1), →(parseformula("q"), parseformula("p")), IŁ4) == false

############################################################################################
#### IH4 ####################################################################################
############################################################################################

using SoleLogics.ManyValuedLogics: H4

IH4 = convert(FiniteIndexFLewAlgebra, H4)

############################################################################################
## Base cases ##############################################################################
############################################################################################

for i ∈ getdomain(IH4)
    for j ∈ getdomain(IH4)
        @test alphasat(i, j, IH4) == alphaprove(i, j, IH4)
        for k ∈ getdomain(IH4)
            @test alphasat(i, ∨(j,k), IH4) == alphaprove(i, ∨(j,k), IH4)
            @test alphasat(i, ∧(j,k), IH4) == alphaprove(i, ∧(j,k), IH4)
            @test alphasat(i, →(j,k), IH4) == alphaprove(i, →(j,k), IH4)
        end
    end
end

@test alphaprove(FiniteIndexTruth(2), parseformula("p"), IH4) == true
@test alphaprove(FiniteIndexTruth(3), parseformula("p"), IH4) == false
@test alphaprove(FiniteIndexTruth(4), parseformula("p"), IH4) == false
@test alphaprove(FiniteIndexTruth(1), parseformula("p"), IH4) == false

############################################################################################
## (Strong) disjuction #####################################################################
############################################################################################

@test alphaprove(FiniteIndexTruth(2), ∨(parseformula("p"), FiniteIndexTruth(2)), IH4) == true
@test alphaprove(FiniteIndexTruth(2), ∨(parseformula("p"), FiniteIndexTruth(3)), IH4) == true
@test alphaprove(FiniteIndexTruth(2), ∨(parseformula("p"), FiniteIndexTruth(4)), IH4) == true
@test alphaprove(FiniteIndexTruth(2), ∨(parseformula("p"), FiniteIndexTruth(1)), IH4) == true
@test alphaprove(FiniteIndexTruth(3), ∨(parseformula("p"), FiniteIndexTruth(2)), IH4) == false
@test alphaprove(FiniteIndexTruth(3), ∨(parseformula("p"), FiniteIndexTruth(3)), IH4) == true
@test alphaprove(FiniteIndexTruth(3), ∨(parseformula("p"), FiniteIndexTruth(4)), IH4) == false
@test alphaprove(FiniteIndexTruth(3), ∨(parseformula("p"), FiniteIndexTruth(1)), IH4) == true
@test alphaprove(FiniteIndexTruth(4), ∨(parseformula("p"), FiniteIndexTruth(2)), IH4) == false
@test alphaprove(FiniteIndexTruth(4), ∨(parseformula("p"), FiniteIndexTruth(3)), IH4) == false
@test alphaprove(FiniteIndexTruth(4), ∨(parseformula("p"), FiniteIndexTruth(4)), IH4) == true
@test alphaprove(FiniteIndexTruth(4), ∨(parseformula("p"), FiniteIndexTruth(1)), IH4) == true
@test alphaprove(FiniteIndexTruth(1), ∨(parseformula("p"), FiniteIndexTruth(2)), IH4) == false
@test alphaprove(FiniteIndexTruth(1), ∨(parseformula("p"), FiniteIndexTruth(3)), IH4) == false
@test alphaprove(FiniteIndexTruth(1), ∨(parseformula("p"), FiniteIndexTruth(4)), IH4) == false
@test alphaprove(FiniteIndexTruth(1), ∨(parseformula("p"), FiniteIndexTruth(1)), IH4) == true

@test alphaprove(FiniteIndexTruth(2), ∨(FiniteIndexTruth(2), parseformula("p")), IH4) == true 
@test alphaprove(FiniteIndexTruth(2), ∨(FiniteIndexTruth(3), parseformula("p")), IH4) == true 
@test alphaprove(FiniteIndexTruth(2), ∨(FiniteIndexTruth(4), parseformula("p")), IH4) == true 
@test alphaprove(FiniteIndexTruth(2), ∨(FiniteIndexTruth(1), parseformula("p")), IH4) == true 
@test alphaprove(FiniteIndexTruth(3), ∨(FiniteIndexTruth(2), parseformula("p")), IH4) == false
@test alphaprove(FiniteIndexTruth(3), ∨(FiniteIndexTruth(3), parseformula("p")), IH4) == true 
@test alphaprove(FiniteIndexTruth(3), ∨(FiniteIndexTruth(4), parseformula("p")), IH4) == false 
@test alphaprove(FiniteIndexTruth(3), ∨(FiniteIndexTruth(1), parseformula("p")), IH4) == true 
@test alphaprove(FiniteIndexTruth(4), ∨(FiniteIndexTruth(2), parseformula("p")), IH4) == false 
@test alphaprove(FiniteIndexTruth(4), ∨(FiniteIndexTruth(3), parseformula("p")), IH4) == false 
@test alphaprove(FiniteIndexTruth(4), ∨(FiniteIndexTruth(4), parseformula("p")), IH4) == true 
@test alphaprove(FiniteIndexTruth(4), ∨(FiniteIndexTruth(1), parseformula("p")), IH4) == true 
@test alphaprove(FiniteIndexTruth(1), ∨(FiniteIndexTruth(2), parseformula("p")), IH4) == false 
@test alphaprove(FiniteIndexTruth(1), ∨(FiniteIndexTruth(3), parseformula("p")), IH4) == false 
@test alphaprove(FiniteIndexTruth(1), ∨(FiniteIndexTruth(4), parseformula("p")), IH4) == false 
@test alphaprove(FiniteIndexTruth(1), ∨(FiniteIndexTruth(1), parseformula("p")), IH4) == true 

@test alphaprove(FiniteIndexTruth(2), ∨(parseformula("p"), parseformula("p")), IH4) == true
@test alphaprove(FiniteIndexTruth(3), ∨(parseformula("p"), parseformula("p")), IH4) == false
@test alphaprove(FiniteIndexTruth(4), ∨(parseformula("p"), parseformula("p")), IH4) == false
@test alphaprove(FiniteIndexTruth(1), ∨(parseformula("p"), parseformula("p")), IH4) == false

@test alphaprove(FiniteIndexTruth(2), ∨(parseformula("p"), parseformula("q")), IH4) == true
@test alphaprove(FiniteIndexTruth(3), ∨(parseformula("p"), parseformula("q")), IH4) == false
@test alphaprove(FiniteIndexTruth(4), ∨(parseformula("p"), parseformula("q")), IH4) == false
@test alphaprove(FiniteIndexTruth(1), ∨(parseformula("p"), parseformula("q")), IH4) == false

@test alphaprove(FiniteIndexTruth(2), ∨(parseformula("q"), parseformula("p")), IH4) == true
@test alphaprove(FiniteIndexTruth(3), ∨(parseformula("q"), parseformula("p")), IH4) == false
@test alphaprove(FiniteIndexTruth(4), ∨(parseformula("q"), parseformula("p")), IH4) == false
@test alphaprove(FiniteIndexTruth(1), ∨(parseformula("q"), parseformula("p")), IH4) == false

############################################################################################
## (Strong) conjunction ####################################################################
############################################################################################

@test alphaprove(FiniteIndexTruth(2), ∧(parseformula("p"), FiniteIndexTruth(2)), IH4) == true
@test alphaprove(FiniteIndexTruth(2), ∧(parseformula("p"), FiniteIndexTruth(3)), IH4) == true
@test alphaprove(FiniteIndexTruth(2), ∧(parseformula("p"), FiniteIndexTruth(4)), IH4) == true
@test alphaprove(FiniteIndexTruth(2), ∧(parseformula("p"), FiniteIndexTruth(1)), IH4) == true
@test alphaprove(FiniteIndexTruth(3), ∧(parseformula("p"), FiniteIndexTruth(2)), IH4) == false
@test alphaprove(FiniteIndexTruth(3), ∧(parseformula("p"), FiniteIndexTruth(3)), IH4) == false
@test alphaprove(FiniteIndexTruth(3), ∧(parseformula("p"), FiniteIndexTruth(4)), IH4) == false
@test alphaprove(FiniteIndexTruth(3), ∧(parseformula("p"), FiniteIndexTruth(1)), IH4) == false
@test alphaprove(FiniteIndexTruth(4), ∧(parseformula("p"), FiniteIndexTruth(2)), IH4) == false
@test alphaprove(FiniteIndexTruth(4), ∧(parseformula("p"), FiniteIndexTruth(3)), IH4) == false
@test alphaprove(FiniteIndexTruth(4), ∧(parseformula("p"), FiniteIndexTruth(4)), IH4) == false
@test alphaprove(FiniteIndexTruth(4), ∧(parseformula("p"), FiniteIndexTruth(1)), IH4) == false
@test alphaprove(FiniteIndexTruth(1), ∧(parseformula("p"), FiniteIndexTruth(2)), IH4) == false
@test alphaprove(FiniteIndexTruth(1), ∧(parseformula("p"), FiniteIndexTruth(3)), IH4) == false
@test alphaprove(FiniteIndexTruth(1), ∧(parseformula("p"), FiniteIndexTruth(4)), IH4) == false
@test alphaprove(FiniteIndexTruth(1), ∧(parseformula("p"), FiniteIndexTruth(1)), IH4) == false

@test alphaprove(FiniteIndexTruth(2), ∧(FiniteIndexTruth(2), parseformula("p")), IH4) == true 
@test alphaprove(FiniteIndexTruth(2), ∧(FiniteIndexTruth(3), parseformula("p")), IH4) == true 
@test alphaprove(FiniteIndexTruth(2), ∧(FiniteIndexTruth(4), parseformula("p")), IH4) == true 
@test alphaprove(FiniteIndexTruth(2), ∧(FiniteIndexTruth(1), parseformula("p")), IH4) == true 
@test alphaprove(FiniteIndexTruth(3), ∧(FiniteIndexTruth(2), parseformula("p")), IH4) == false
@test alphaprove(FiniteIndexTruth(3), ∧(FiniteIndexTruth(3), parseformula("p")), IH4) == false 
@test alphaprove(FiniteIndexTruth(3), ∧(FiniteIndexTruth(4), parseformula("p")), IH4) == false 
@test alphaprove(FiniteIndexTruth(3), ∧(FiniteIndexTruth(1), parseformula("p")), IH4) == false 
@test alphaprove(FiniteIndexTruth(4), ∧(FiniteIndexTruth(2), parseformula("p")), IH4) == false 
@test alphaprove(FiniteIndexTruth(4), ∧(FiniteIndexTruth(3), parseformula("p")), IH4) == false 
@test alphaprove(FiniteIndexTruth(4), ∧(FiniteIndexTruth(4), parseformula("p")), IH4) == false 
@test alphaprove(FiniteIndexTruth(4), ∧(FiniteIndexTruth(1), parseformula("p")), IH4) == false 
@test alphaprove(FiniteIndexTruth(1), ∧(FiniteIndexTruth(2), parseformula("p")), IH4) == false 
@test alphaprove(FiniteIndexTruth(1), ∧(FiniteIndexTruth(3), parseformula("p")), IH4) == false 
@test alphaprove(FiniteIndexTruth(1), ∧(FiniteIndexTruth(4), parseformula("p")), IH4) == false 
@test alphaprove(FiniteIndexTruth(1), ∧(FiniteIndexTruth(1), parseformula("p")), IH4) == false 

@test alphaprove(FiniteIndexTruth(2), ∧(parseformula("p"), parseformula("p")), IH4) == true
@test alphaprove(FiniteIndexTruth(3), ∧(parseformula("p"), parseformula("p")), IH4) == false
@test alphaprove(FiniteIndexTruth(4), ∧(parseformula("p"), parseformula("p")), IH4) == false
@test alphaprove(FiniteIndexTruth(1), ∧(parseformula("p"), parseformula("p")), IH4) == false

@test alphaprove(FiniteIndexTruth(2), ∧(parseformula("p"), parseformula("q")), IH4) == true
@test alphaprove(FiniteIndexTruth(3), ∧(parseformula("p"), parseformula("q")), IH4) == false
@test alphaprove(FiniteIndexTruth(4), ∧(parseformula("p"), parseformula("q")), IH4) == false
@test alphaprove(FiniteIndexTruth(1), ∧(parseformula("p"), parseformula("q")), IH4) == false

@test alphaprove(FiniteIndexTruth(2), ∧(parseformula("q"), parseformula("p")), IH4) == true
@test alphaprove(FiniteIndexTruth(3), ∧(parseformula("q"), parseformula("p")), IH4) == false
@test alphaprove(FiniteIndexTruth(4), ∧(parseformula("q"), parseformula("p")), IH4) == false
@test alphaprove(FiniteIndexTruth(1), ∧(parseformula("q"), parseformula("p")), IH4) == false

############################################################################################
## Implication #############################################################################
############################################################################################

@test alphaprove(FiniteIndexTruth(2), →(parseformula("p"), FiniteIndexTruth(2)), IH4) == true
@test alphaprove(FiniteIndexTruth(2), →(parseformula("p"), FiniteIndexTruth(3)), IH4) == true
@test alphaprove(FiniteIndexTruth(2), →(parseformula("p"), FiniteIndexTruth(4)), IH4) == true
@test alphaprove(FiniteIndexTruth(2), →(parseformula("p"), FiniteIndexTruth(1)), IH4) == true
@test alphaprove(FiniteIndexTruth(3), →(parseformula("p"), FiniteIndexTruth(2)), IH4) == false
@test alphaprove(FiniteIndexTruth(3), →(parseformula("p"), FiniteIndexTruth(3)), IH4) == true
@test alphaprove(FiniteIndexTruth(3), →(parseformula("p"), FiniteIndexTruth(4)), IH4) == false
@test alphaprove(FiniteIndexTruth(3), →(parseformula("p"), FiniteIndexTruth(1)), IH4) == true
@test alphaprove(FiniteIndexTruth(4), →(parseformula("p"), FiniteIndexTruth(2)), IH4) == false
@test alphaprove(FiniteIndexTruth(4), →(parseformula("p"), FiniteIndexTruth(3)), IH4) == false
@test alphaprove(FiniteIndexTruth(4), →(parseformula("p"), FiniteIndexTruth(4)), IH4) == true
@test alphaprove(FiniteIndexTruth(4), →(parseformula("p"), FiniteIndexTruth(1)), IH4) == true
@test alphaprove(FiniteIndexTruth(1), →(parseformula("p"), FiniteIndexTruth(2)), IH4) == false
@test alphaprove(FiniteIndexTruth(1), →(parseformula("p"), FiniteIndexTruth(3)), IH4) == false
@test alphaprove(FiniteIndexTruth(1), →(parseformula("p"), FiniteIndexTruth(4)), IH4) == false
@test alphaprove(FiniteIndexTruth(1), →(parseformula("p"), FiniteIndexTruth(1)), IH4) == true

@test alphaprove(FiniteIndexTruth(2), →(FiniteIndexTruth(2), parseformula("p")), IH4) == true
@test alphaprove(FiniteIndexTruth(2), →(FiniteIndexTruth(3), parseformula("p")), IH4) == true
@test alphaprove(FiniteIndexTruth(2), →(FiniteIndexTruth(4), parseformula("p")), IH4) == true
@test alphaprove(FiniteIndexTruth(2), →(FiniteIndexTruth(1), parseformula("p")), IH4) == true
@test alphaprove(FiniteIndexTruth(3), →(FiniteIndexTruth(2), parseformula("p")), IH4) == true
@test alphaprove(FiniteIndexTruth(3), →(FiniteIndexTruth(3), parseformula("p")), IH4) == false
@test alphaprove(FiniteIndexTruth(3), →(FiniteIndexTruth(4), parseformula("p")), IH4) == true
@test alphaprove(FiniteIndexTruth(3), →(FiniteIndexTruth(1), parseformula("p")), IH4) == false
@test alphaprove(FiniteIndexTruth(4), →(FiniteIndexTruth(2), parseformula("p")), IH4) == true
@test alphaprove(FiniteIndexTruth(4), →(FiniteIndexTruth(3), parseformula("p")), IH4) == true
@test alphaprove(FiniteIndexTruth(4), →(FiniteIndexTruth(4), parseformula("p")), IH4) == false
@test alphaprove(FiniteIndexTruth(4), →(FiniteIndexTruth(1), parseformula("p")), IH4) == false
@test alphaprove(FiniteIndexTruth(1), →(FiniteIndexTruth(2), parseformula("p")), IH4) == true
@test alphaprove(FiniteIndexTruth(1), →(FiniteIndexTruth(3), parseformula("p")), IH4) == false
@test alphaprove(FiniteIndexTruth(1), →(FiniteIndexTruth(4), parseformula("p")), IH4) == false
@test alphaprove(FiniteIndexTruth(1), →(FiniteIndexTruth(1), parseformula("p")), IH4) == false

@test alphaprove(FiniteIndexTruth(2), →(parseformula("p"), parseformula("p")), IH4) == true
@test alphaprove(FiniteIndexTruth(3), →(parseformula("p"), parseformula("p")), IH4) == true
@test alphaprove(FiniteIndexTruth(4), →(parseformula("p"), parseformula("p")), IH4) == true
@test alphaprove(FiniteIndexTruth(1), →(parseformula("p"), parseformula("p")), IH4) == true

@test alphaprove(FiniteIndexTruth(2), →(parseformula("p"), parseformula("q")), IH4) == true
@test alphaprove(FiniteIndexTruth(3), →(parseformula("p"), parseformula("q")), IH4) == false
@test alphaprove(FiniteIndexTruth(4), →(parseformula("p"), parseformula("q")), IH4) == false
@test alphaprove(FiniteIndexTruth(1), →(parseformula("p"), parseformula("q")), IH4) == false

@test alphaprove(FiniteIndexTruth(2), →(parseformula("q"), parseformula("p")), IH4) == true
@test alphaprove(FiniteIndexTruth(3), →(parseformula("q"), parseformula("p")), IH4) == false
@test alphaprove(FiniteIndexTruth(4), →(parseformula("q"), parseformula("p")), IH4) == false
@test alphaprove(FiniteIndexTruth(1), →(parseformula("q"), parseformula("p")), IH4) == false
