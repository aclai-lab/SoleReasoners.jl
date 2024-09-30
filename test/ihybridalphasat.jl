###########################################################################################
### IG4 ####################################################################################
###########################################################################################

using SoleLogics.ManyValuedLogics: G4, FiniteIndexTruth, FiniteIndexFLewAlgebra

IG4 = convert(FiniteIndexFLewAlgebra, G4)

############################################################################################
## Base cases ##############################################################################
############################################################################################

@test hybridalphasat(FiniteIndexTruth(2), FiniteIndexTruth(2), IG4) == true
@test hybridalphasat(FiniteIndexTruth(2), FiniteIndexTruth(3), IG4) == true
@test hybridalphasat(FiniteIndexTruth(2), FiniteIndexTruth(4), IG4) == true
@test hybridalphasat(FiniteIndexTruth(2), FiniteIndexTruth(1), IG4) == true
@test hybridalphasat(FiniteIndexTruth(3), FiniteIndexTruth(2), IG4) == false
@test hybridalphasat(FiniteIndexTruth(3), FiniteIndexTruth(3), IG4) == true
@test hybridalphasat(FiniteIndexTruth(3), FiniteIndexTruth(4), IG4) == true
@test hybridalphasat(FiniteIndexTruth(3), FiniteIndexTruth(1), IG4) == true
@test hybridalphasat(FiniteIndexTruth(4), FiniteIndexTruth(2), IG4) == false
@test hybridalphasat(FiniteIndexTruth(4), FiniteIndexTruth(3), IG4) == false
@test hybridalphasat(FiniteIndexTruth(4), FiniteIndexTruth(4), IG4) == true
@test hybridalphasat(FiniteIndexTruth(4), FiniteIndexTruth(1), IG4) == true
@test hybridalphasat(FiniteIndexTruth(1), FiniteIndexTruth(2), IG4) == false
@test hybridalphasat(FiniteIndexTruth(1), FiniteIndexTruth(3), IG4) == false
@test hybridalphasat(FiniteIndexTruth(1), FiniteIndexTruth(4), IG4) == false
@test hybridalphasat(FiniteIndexTruth(1), FiniteIndexTruth(1), IG4) == true

@test hybridalphasat(FiniteIndexTruth(2), parseformula("p"), IG4) == true
@test hybridalphasat(FiniteIndexTruth(3), parseformula("p"), IG4) == true
@test hybridalphasat(FiniteIndexTruth(4), parseformula("p"), IG4) == true
@test hybridalphasat(FiniteIndexTruth(1), parseformula("p"), IG4) == true

############################################################################################
## (Strong) disjuction #####################################################################
############################################################################################

@test hybridalphasat(FiniteIndexTruth(2), ∨(FiniteIndexTruth(2), FiniteIndexTruth(2)), IG4) == true
@test hybridalphasat(FiniteIndexTruth(2), ∨(FiniteIndexTruth(2), FiniteIndexTruth(3)), IG4) == true
@test hybridalphasat(FiniteIndexTruth(2), ∨(FiniteIndexTruth(2), FiniteIndexTruth(4)), IG4) == true
@test hybridalphasat(FiniteIndexTruth(2), ∨(FiniteIndexTruth(2), FiniteIndexTruth(1)), IG4) == true
@test hybridalphasat(FiniteIndexTruth(2), ∨(FiniteIndexTruth(3), FiniteIndexTruth(2)), IG4) == true
@test hybridalphasat(FiniteIndexTruth(2), ∨(FiniteIndexTruth(3), FiniteIndexTruth(3)), IG4) == true
@test hybridalphasat(FiniteIndexTruth(2), ∨(FiniteIndexTruth(3), FiniteIndexTruth(4)), IG4) == true
@test hybridalphasat(FiniteIndexTruth(2), ∨(FiniteIndexTruth(3), FiniteIndexTruth(1)), IG4) == true
@test hybridalphasat(FiniteIndexTruth(2), ∨(FiniteIndexTruth(4), FiniteIndexTruth(2)), IG4) == true
@test hybridalphasat(FiniteIndexTruth(2), ∨(FiniteIndexTruth(4), FiniteIndexTruth(3)), IG4) == true
@test hybridalphasat(FiniteIndexTruth(2), ∨(FiniteIndexTruth(4), FiniteIndexTruth(4)), IG4) == true
@test hybridalphasat(FiniteIndexTruth(2), ∨(FiniteIndexTruth(4), FiniteIndexTruth(1)), IG4) == true
@test hybridalphasat(FiniteIndexTruth(2), ∨(FiniteIndexTruth(1), FiniteIndexTruth(2)), IG4) == true
@test hybridalphasat(FiniteIndexTruth(2), ∨(FiniteIndexTruth(1), FiniteIndexTruth(3)), IG4) == true
@test hybridalphasat(FiniteIndexTruth(2), ∨(FiniteIndexTruth(1), FiniteIndexTruth(4)), IG4) == true
@test hybridalphasat(FiniteIndexTruth(2), ∨(FiniteIndexTruth(1), FiniteIndexTruth(1)), IG4) == true

@test hybridalphasat(FiniteIndexTruth(3), ∨(FiniteIndexTruth(2), FiniteIndexTruth(2)), IG4) == false
@test hybridalphasat(FiniteIndexTruth(3), ∨(FiniteIndexTruth(2), FiniteIndexTruth(3)), IG4) == true
@test hybridalphasat(FiniteIndexTruth(3), ∨(FiniteIndexTruth(2), FiniteIndexTruth(4)), IG4) == true
@test hybridalphasat(FiniteIndexTruth(3), ∨(FiniteIndexTruth(2), FiniteIndexTruth(1)), IG4) == true
@test hybridalphasat(FiniteIndexTruth(3), ∨(FiniteIndexTruth(3), FiniteIndexTruth(2)), IG4) == true
@test hybridalphasat(FiniteIndexTruth(3), ∨(FiniteIndexTruth(3), FiniteIndexTruth(3)), IG4) == true
@test hybridalphasat(FiniteIndexTruth(3), ∨(FiniteIndexTruth(3), FiniteIndexTruth(4)), IG4) == true
@test hybridalphasat(FiniteIndexTruth(3), ∨(FiniteIndexTruth(3), FiniteIndexTruth(1)), IG4) == true
@test hybridalphasat(FiniteIndexTruth(3), ∨(FiniteIndexTruth(4), FiniteIndexTruth(2)), IG4) == true
@test hybridalphasat(FiniteIndexTruth(3), ∨(FiniteIndexTruth(4), FiniteIndexTruth(3)), IG4) == true
@test hybridalphasat(FiniteIndexTruth(3), ∨(FiniteIndexTruth(4), FiniteIndexTruth(4)), IG4) == true
@test hybridalphasat(FiniteIndexTruth(3), ∨(FiniteIndexTruth(4), FiniteIndexTruth(1)), IG4) == true
@test hybridalphasat(FiniteIndexTruth(3), ∨(FiniteIndexTruth(1), FiniteIndexTruth(2)), IG4) == true
@test hybridalphasat(FiniteIndexTruth(3), ∨(FiniteIndexTruth(1), FiniteIndexTruth(3)), IG4) == true
@test hybridalphasat(FiniteIndexTruth(3), ∨(FiniteIndexTruth(1), FiniteIndexTruth(4)), IG4) == true
@test hybridalphasat(FiniteIndexTruth(3), ∨(FiniteIndexTruth(1), FiniteIndexTruth(1)), IG4) == true

@test hybridalphasat(FiniteIndexTruth(4), ∨(FiniteIndexTruth(2), FiniteIndexTruth(2)), IG4) == false
@test hybridalphasat(FiniteIndexTruth(4), ∨(FiniteIndexTruth(2), FiniteIndexTruth(3)), IG4) == false
@test hybridalphasat(FiniteIndexTruth(4), ∨(FiniteIndexTruth(2), FiniteIndexTruth(4)), IG4) == true
@test hybridalphasat(FiniteIndexTruth(4), ∨(FiniteIndexTruth(2), FiniteIndexTruth(1)), IG4) == true
@test hybridalphasat(FiniteIndexTruth(4), ∨(FiniteIndexTruth(3), FiniteIndexTruth(2)), IG4) == false
@test hybridalphasat(FiniteIndexTruth(4), ∨(FiniteIndexTruth(3), FiniteIndexTruth(3)), IG4) == false
@test hybridalphasat(FiniteIndexTruth(4), ∨(FiniteIndexTruth(3), FiniteIndexTruth(4)), IG4) == true
@test hybridalphasat(FiniteIndexTruth(4), ∨(FiniteIndexTruth(3), FiniteIndexTruth(1)), IG4) == true
@test hybridalphasat(FiniteIndexTruth(4), ∨(FiniteIndexTruth(4), FiniteIndexTruth(2)), IG4) == true
@test hybridalphasat(FiniteIndexTruth(4), ∨(FiniteIndexTruth(4), FiniteIndexTruth(3)), IG4) == true
@test hybridalphasat(FiniteIndexTruth(4), ∨(FiniteIndexTruth(4), FiniteIndexTruth(4)), IG4) == true
@test hybridalphasat(FiniteIndexTruth(4), ∨(FiniteIndexTruth(4), FiniteIndexTruth(1)), IG4) == true
@test hybridalphasat(FiniteIndexTruth(4), ∨(FiniteIndexTruth(1), FiniteIndexTruth(2)), IG4) == true
@test hybridalphasat(FiniteIndexTruth(4), ∨(FiniteIndexTruth(1), FiniteIndexTruth(3)), IG4) == true
@test hybridalphasat(FiniteIndexTruth(4), ∨(FiniteIndexTruth(1), FiniteIndexTruth(4)), IG4) == true
@test hybridalphasat(FiniteIndexTruth(4), ∨(FiniteIndexTruth(1), FiniteIndexTruth(1)), IG4) == true

@test hybridalphasat(FiniteIndexTruth(1), ∨(FiniteIndexTruth(2), FiniteIndexTruth(2)), IG4) == false
@test hybridalphasat(FiniteIndexTruth(1), ∨(FiniteIndexTruth(2), FiniteIndexTruth(3)), IG4) == false
@test hybridalphasat(FiniteIndexTruth(1), ∨(FiniteIndexTruth(2), FiniteIndexTruth(4)), IG4) == false
@test hybridalphasat(FiniteIndexTruth(1), ∨(FiniteIndexTruth(2), FiniteIndexTruth(1)), IG4) == true
@test hybridalphasat(FiniteIndexTruth(1), ∨(FiniteIndexTruth(3), FiniteIndexTruth(2)), IG4) == false
@test hybridalphasat(FiniteIndexTruth(1), ∨(FiniteIndexTruth(3), FiniteIndexTruth(3)), IG4) == false
@test hybridalphasat(FiniteIndexTruth(1), ∨(FiniteIndexTruth(3), FiniteIndexTruth(4)), IG4) == false
@test hybridalphasat(FiniteIndexTruth(1), ∨(FiniteIndexTruth(3), FiniteIndexTruth(1)), IG4) == true
@test hybridalphasat(FiniteIndexTruth(1), ∨(FiniteIndexTruth(4), FiniteIndexTruth(2)), IG4) == false
@test hybridalphasat(FiniteIndexTruth(1), ∨(FiniteIndexTruth(4), FiniteIndexTruth(3)), IG4) == false
@test hybridalphasat(FiniteIndexTruth(1), ∨(FiniteIndexTruth(4), FiniteIndexTruth(4)), IG4) == false
@test hybridalphasat(FiniteIndexTruth(1), ∨(FiniteIndexTruth(4), FiniteIndexTruth(1)), IG4) == true
@test hybridalphasat(FiniteIndexTruth(1), ∨(FiniteIndexTruth(1), FiniteIndexTruth(2)), IG4) == true
@test hybridalphasat(FiniteIndexTruth(1), ∨(FiniteIndexTruth(1), FiniteIndexTruth(3)), IG4) == true
@test hybridalphasat(FiniteIndexTruth(1), ∨(FiniteIndexTruth(1), FiniteIndexTruth(4)), IG4) == true
@test hybridalphasat(FiniteIndexTruth(1), ∨(FiniteIndexTruth(1), FiniteIndexTruth(1)), IG4) == true

@test hybridalphasat(FiniteIndexTruth(2), ∨(parseformula("p"), FiniteIndexTruth(2)), IG4) == true
@test hybridalphasat(FiniteIndexTruth(2), ∨(parseformula("p"), FiniteIndexTruth(3)), IG4) == true
@test hybridalphasat(FiniteIndexTruth(2), ∨(parseformula("p"), FiniteIndexTruth(4)), IG4) == true
@test hybridalphasat(FiniteIndexTruth(2), ∨(parseformula("p"), FiniteIndexTruth(1)), IG4) == true
@test hybridalphasat(FiniteIndexTruth(3), ∨(parseformula("p"), FiniteIndexTruth(2)), IG4) == true
@test hybridalphasat(FiniteIndexTruth(3), ∨(parseformula("p"), FiniteIndexTruth(3)), IG4) == true
@test hybridalphasat(FiniteIndexTruth(3), ∨(parseformula("p"), FiniteIndexTruth(4)), IG4) == true
@test hybridalphasat(FiniteIndexTruth(3), ∨(parseformula("p"), FiniteIndexTruth(1)), IG4) == true
@test hybridalphasat(FiniteIndexTruth(4), ∨(parseformula("p"), FiniteIndexTruth(2)), IG4) == true
@test hybridalphasat(FiniteIndexTruth(4), ∨(parseformula("p"), FiniteIndexTruth(3)), IG4) == true
@test hybridalphasat(FiniteIndexTruth(4), ∨(parseformula("p"), FiniteIndexTruth(4)), IG4) == true
@test hybridalphasat(FiniteIndexTruth(4), ∨(parseformula("p"), FiniteIndexTruth(1)), IG4) == true
@test hybridalphasat(FiniteIndexTruth(1), ∨(parseformula("p"), FiniteIndexTruth(2)), IG4) == true
@test hybridalphasat(FiniteIndexTruth(1), ∨(parseformula("p"), FiniteIndexTruth(3)), IG4) == true
@test hybridalphasat(FiniteIndexTruth(1), ∨(parseformula("p"), FiniteIndexTruth(4)), IG4) == true
@test hybridalphasat(FiniteIndexTruth(1), ∨(parseformula("p"), FiniteIndexTruth(1)), IG4) == true

@test hybridalphasat(FiniteIndexTruth(2), ∨(FiniteIndexTruth(2), parseformula("p")), IG4) == true
@test hybridalphasat(FiniteIndexTruth(2), ∨(FiniteIndexTruth(3), parseformula("p")), IG4) == true
@test hybridalphasat(FiniteIndexTruth(2), ∨(FiniteIndexTruth(4), parseformula("p")), IG4) == true
@test hybridalphasat(FiniteIndexTruth(2), ∨(FiniteIndexTruth(1), parseformula("p")), IG4) == true
@test hybridalphasat(FiniteIndexTruth(3), ∨(FiniteIndexTruth(2), parseformula("p")), IG4) == true
@test hybridalphasat(FiniteIndexTruth(3), ∨(FiniteIndexTruth(3), parseformula("p")), IG4) == true
@test hybridalphasat(FiniteIndexTruth(3), ∨(FiniteIndexTruth(4), parseformula("p")), IG4) == true
@test hybridalphasat(FiniteIndexTruth(3), ∨(FiniteIndexTruth(1), parseformula("p")), IG4) == true
@test hybridalphasat(FiniteIndexTruth(4), ∨(FiniteIndexTruth(2), parseformula("p")), IG4) == true
@test hybridalphasat(FiniteIndexTruth(4), ∨(FiniteIndexTruth(3), parseformula("p")), IG4) == true
@test hybridalphasat(FiniteIndexTruth(4), ∨(FiniteIndexTruth(4), parseformula("p")), IG4) == true
@test hybridalphasat(FiniteIndexTruth(4), ∨(FiniteIndexTruth(1), parseformula("p")), IG4) == true
@test hybridalphasat(FiniteIndexTruth(1), ∨(FiniteIndexTruth(2), parseformula("p")), IG4) == true
@test hybridalphasat(FiniteIndexTruth(1), ∨(FiniteIndexTruth(3), parseformula("p")), IG4) == true
@test hybridalphasat(FiniteIndexTruth(1), ∨(FiniteIndexTruth(4), parseformula("p")), IG4) == true
@test hybridalphasat(FiniteIndexTruth(1), ∨(FiniteIndexTruth(1), parseformula("p")), IG4) == true

@test hybridalphasat(FiniteIndexTruth(2), ∨(parseformula("p"), parseformula("p")), IG4) == true
@test hybridalphasat(FiniteIndexTruth(3), ∨(parseformula("p"), parseformula("p")), IG4) == true
@test hybridalphasat(FiniteIndexTruth(4), ∨(parseformula("p"), parseformula("p")), IG4) == true
@test hybridalphasat(FiniteIndexTruth(1), ∨(parseformula("p"), parseformula("p")), IG4) == true

@test hybridalphasat(FiniteIndexTruth(2), ∨(parseformula("p"), parseformula("q")), IG4) == true
@test hybridalphasat(FiniteIndexTruth(3), ∨(parseformula("p"), parseformula("q")), IG4) == true
@test hybridalphasat(FiniteIndexTruth(4), ∨(parseformula("p"), parseformula("q")), IG4) == true
@test hybridalphasat(FiniteIndexTruth(1), ∨(parseformula("p"), parseformula("q")), IG4) == true

@test hybridalphasat(FiniteIndexTruth(2), ∨(parseformula("q"), parseformula("q")), IG4) == true
@test hybridalphasat(FiniteIndexTruth(3), ∨(parseformula("q"), parseformula("q")), IG4) == true
@test hybridalphasat(FiniteIndexTruth(4), ∨(parseformula("q"), parseformula("q")), IG4) == true
@test hybridalphasat(FiniteIndexTruth(1), ∨(parseformula("q"), parseformula("q")), IG4) == true

############################################################################################
## (Strong) conjunction ####################################################################
############################################################################################

@test hybridalphasat(FiniteIndexTruth(2), ∧(FiniteIndexTruth(2), FiniteIndexTruth(2)), IG4) == true
@test hybridalphasat(FiniteIndexTruth(2), ∧(FiniteIndexTruth(2), FiniteIndexTruth(3)), IG4) == true
@test hybridalphasat(FiniteIndexTruth(2), ∧(FiniteIndexTruth(2), FiniteIndexTruth(4)), IG4) == true
@test hybridalphasat(FiniteIndexTruth(2), ∧(FiniteIndexTruth(2), FiniteIndexTruth(1)), IG4) == true
@test hybridalphasat(FiniteIndexTruth(2), ∧(FiniteIndexTruth(3), FiniteIndexTruth(2)), IG4) == true
@test hybridalphasat(FiniteIndexTruth(2), ∧(FiniteIndexTruth(3), FiniteIndexTruth(3)), IG4) == true
@test hybridalphasat(FiniteIndexTruth(2), ∧(FiniteIndexTruth(3), FiniteIndexTruth(4)), IG4) == true
@test hybridalphasat(FiniteIndexTruth(2), ∧(FiniteIndexTruth(3), FiniteIndexTruth(1)), IG4) == true
@test hybridalphasat(FiniteIndexTruth(2), ∧(FiniteIndexTruth(4), FiniteIndexTruth(2)), IG4) == true
@test hybridalphasat(FiniteIndexTruth(2), ∧(FiniteIndexTruth(4), FiniteIndexTruth(3)), IG4) == true
@test hybridalphasat(FiniteIndexTruth(2), ∧(FiniteIndexTruth(4), FiniteIndexTruth(4)), IG4) == true
@test hybridalphasat(FiniteIndexTruth(2), ∧(FiniteIndexTruth(4), FiniteIndexTruth(1)), IG4) == true
@test hybridalphasat(FiniteIndexTruth(2), ∧(FiniteIndexTruth(1), FiniteIndexTruth(2)), IG4) == true
@test hybridalphasat(FiniteIndexTruth(2), ∧(FiniteIndexTruth(1), FiniteIndexTruth(3)), IG4) == true
@test hybridalphasat(FiniteIndexTruth(2), ∧(FiniteIndexTruth(1), FiniteIndexTruth(4)), IG4) == true
@test hybridalphasat(FiniteIndexTruth(2), ∧(FiniteIndexTruth(1), FiniteIndexTruth(1)), IG4) == true

@test hybridalphasat(FiniteIndexTruth(3), ∧(FiniteIndexTruth(2), FiniteIndexTruth(2)), IG4) == false
@test hybridalphasat(FiniteIndexTruth(3), ∧(FiniteIndexTruth(2), FiniteIndexTruth(3)), IG4) == false
@test hybridalphasat(FiniteIndexTruth(3), ∧(FiniteIndexTruth(2), FiniteIndexTruth(4)), IG4) == false
@test hybridalphasat(FiniteIndexTruth(3), ∧(FiniteIndexTruth(2), FiniteIndexTruth(1)), IG4) == false
@test hybridalphasat(FiniteIndexTruth(3), ∧(FiniteIndexTruth(3), FiniteIndexTruth(2)), IG4) == false
@test hybridalphasat(FiniteIndexTruth(3), ∧(FiniteIndexTruth(3), FiniteIndexTruth(3)), IG4) == true
@test hybridalphasat(FiniteIndexTruth(3), ∧(FiniteIndexTruth(3), FiniteIndexTruth(4)), IG4) == true
@test hybridalphasat(FiniteIndexTruth(3), ∧(FiniteIndexTruth(3), FiniteIndexTruth(1)), IG4) == true
@test hybridalphasat(FiniteIndexTruth(3), ∧(FiniteIndexTruth(4), FiniteIndexTruth(2)), IG4) == false
@test hybridalphasat(FiniteIndexTruth(3), ∧(FiniteIndexTruth(4), FiniteIndexTruth(3)), IG4) == true
@test hybridalphasat(FiniteIndexTruth(3), ∧(FiniteIndexTruth(4), FiniteIndexTruth(4)), IG4) == true
@test hybridalphasat(FiniteIndexTruth(3), ∧(FiniteIndexTruth(4), FiniteIndexTruth(1)), IG4) == true
@test hybridalphasat(FiniteIndexTruth(3), ∧(FiniteIndexTruth(1), FiniteIndexTruth(2)), IG4) == false
@test hybridalphasat(FiniteIndexTruth(3), ∧(FiniteIndexTruth(1), FiniteIndexTruth(3)), IG4) == true
@test hybridalphasat(FiniteIndexTruth(3), ∧(FiniteIndexTruth(1), FiniteIndexTruth(4)), IG4) == true
@test hybridalphasat(FiniteIndexTruth(3), ∧(FiniteIndexTruth(1), FiniteIndexTruth(1)), IG4) == true

@test hybridalphasat(FiniteIndexTruth(4), ∧(FiniteIndexTruth(2), FiniteIndexTruth(2)), IG4) == false
@test hybridalphasat(FiniteIndexTruth(4), ∧(FiniteIndexTruth(2), FiniteIndexTruth(3)), IG4) == false
@test hybridalphasat(FiniteIndexTruth(4), ∧(FiniteIndexTruth(2), FiniteIndexTruth(4)), IG4) == false
@test hybridalphasat(FiniteIndexTruth(4), ∧(FiniteIndexTruth(2), FiniteIndexTruth(1)), IG4) == false
@test hybridalphasat(FiniteIndexTruth(4), ∧(FiniteIndexTruth(3), FiniteIndexTruth(2)), IG4) == false
@test hybridalphasat(FiniteIndexTruth(4), ∧(FiniteIndexTruth(3), FiniteIndexTruth(3)), IG4) == false
@test hybridalphasat(FiniteIndexTruth(4), ∧(FiniteIndexTruth(3), FiniteIndexTruth(4)), IG4) == false
@test hybridalphasat(FiniteIndexTruth(4), ∧(FiniteIndexTruth(3), FiniteIndexTruth(1)), IG4) == false
@test hybridalphasat(FiniteIndexTruth(4), ∧(FiniteIndexTruth(4), FiniteIndexTruth(2)), IG4) == false
@test hybridalphasat(FiniteIndexTruth(4), ∧(FiniteIndexTruth(4), FiniteIndexTruth(3)), IG4) == false
@test hybridalphasat(FiniteIndexTruth(4), ∧(FiniteIndexTruth(4), FiniteIndexTruth(4)), IG4) == true
@test hybridalphasat(FiniteIndexTruth(4), ∧(FiniteIndexTruth(4), FiniteIndexTruth(1)), IG4) == true
@test hybridalphasat(FiniteIndexTruth(4), ∧(FiniteIndexTruth(1), FiniteIndexTruth(2)), IG4) == false
@test hybridalphasat(FiniteIndexTruth(4), ∧(FiniteIndexTruth(1), FiniteIndexTruth(3)), IG4) == false
@test hybridalphasat(FiniteIndexTruth(4), ∧(FiniteIndexTruth(1), FiniteIndexTruth(4)), IG4) == true
@test hybridalphasat(FiniteIndexTruth(4), ∧(FiniteIndexTruth(1), FiniteIndexTruth(1)), IG4) == true

@test hybridalphasat(FiniteIndexTruth(1), ∧(FiniteIndexTruth(2), FiniteIndexTruth(2)), IG4) == false
@test hybridalphasat(FiniteIndexTruth(1), ∧(FiniteIndexTruth(2), FiniteIndexTruth(3)), IG4) == false
@test hybridalphasat(FiniteIndexTruth(1), ∧(FiniteIndexTruth(2), FiniteIndexTruth(4)), IG4) == false
@test hybridalphasat(FiniteIndexTruth(1), ∧(FiniteIndexTruth(2), FiniteIndexTruth(1)), IG4) == false
@test hybridalphasat(FiniteIndexTruth(1), ∧(FiniteIndexTruth(3), FiniteIndexTruth(2)), IG4) == false
@test hybridalphasat(FiniteIndexTruth(1), ∧(FiniteIndexTruth(3), FiniteIndexTruth(3)), IG4) == false
@test hybridalphasat(FiniteIndexTruth(1), ∧(FiniteIndexTruth(3), FiniteIndexTruth(4)), IG4) == false
@test hybridalphasat(FiniteIndexTruth(1), ∧(FiniteIndexTruth(3), FiniteIndexTruth(1)), IG4) == false
@test hybridalphasat(FiniteIndexTruth(1), ∧(FiniteIndexTruth(4), FiniteIndexTruth(2)), IG4) == false
@test hybridalphasat(FiniteIndexTruth(1), ∧(FiniteIndexTruth(4), FiniteIndexTruth(3)), IG4) == false
@test hybridalphasat(FiniteIndexTruth(1), ∧(FiniteIndexTruth(4), FiniteIndexTruth(4)), IG4) == false
@test hybridalphasat(FiniteIndexTruth(1), ∧(FiniteIndexTruth(4), FiniteIndexTruth(1)), IG4) == false
@test hybridalphasat(FiniteIndexTruth(1), ∧(FiniteIndexTruth(1), FiniteIndexTruth(2)), IG4) == false
@test hybridalphasat(FiniteIndexTruth(1), ∧(FiniteIndexTruth(1), FiniteIndexTruth(3)), IG4) == false
@test hybridalphasat(FiniteIndexTruth(1), ∧(FiniteIndexTruth(1), FiniteIndexTruth(4)), IG4) == false
@test hybridalphasat(FiniteIndexTruth(1), ∧(FiniteIndexTruth(1), FiniteIndexTruth(1)), IG4) == true

@test hybridalphasat(FiniteIndexTruth(2), ∧(parseformula("p"), FiniteIndexTruth(2)), IG4) == true
@test hybridalphasat(FiniteIndexTruth(2), ∧(parseformula("p"), FiniteIndexTruth(3)), IG4) == true
@test hybridalphasat(FiniteIndexTruth(2), ∧(parseformula("p"), FiniteIndexTruth(4)), IG4) == true
@test hybridalphasat(FiniteIndexTruth(2), ∧(parseformula("p"), FiniteIndexTruth(1)), IG4) == true
@test hybridalphasat(FiniteIndexTruth(3), ∧(parseformula("p"), FiniteIndexTruth(2)), IG4) == false
@test hybridalphasat(FiniteIndexTruth(3), ∧(parseformula("p"), FiniteIndexTruth(3)), IG4) == true
@test hybridalphasat(FiniteIndexTruth(3), ∧(parseformula("p"), FiniteIndexTruth(4)), IG4) == true
@test hybridalphasat(FiniteIndexTruth(3), ∧(parseformula("p"), FiniteIndexTruth(1)), IG4) == true
@test hybridalphasat(FiniteIndexTruth(4), ∧(parseformula("p"), FiniteIndexTruth(2)), IG4) == false
@test hybridalphasat(FiniteIndexTruth(4), ∧(parseformula("p"), FiniteIndexTruth(3)), IG4) == false
@test hybridalphasat(FiniteIndexTruth(4), ∧(parseformula("p"), FiniteIndexTruth(4)), IG4) == true
@test hybridalphasat(FiniteIndexTruth(4), ∧(parseformula("p"), FiniteIndexTruth(1)), IG4) == true
@test hybridalphasat(FiniteIndexTruth(1), ∧(parseformula("p"), FiniteIndexTruth(2)), IG4) == false
@test hybridalphasat(FiniteIndexTruth(1), ∧(parseformula("p"), FiniteIndexTruth(3)), IG4) == false
@test hybridalphasat(FiniteIndexTruth(1), ∧(parseformula("p"), FiniteIndexTruth(4)), IG4) == false
@test hybridalphasat(FiniteIndexTruth(1), ∧(parseformula("p"), FiniteIndexTruth(1)), IG4) == true

@test hybridalphasat(FiniteIndexTruth(2), ∧(FiniteIndexTruth(2), parseformula("p")), IG4) == true
@test hybridalphasat(FiniteIndexTruth(2), ∧(FiniteIndexTruth(3), parseformula("p")), IG4) == true
@test hybridalphasat(FiniteIndexTruth(2), ∧(FiniteIndexTruth(4), parseformula("p")), IG4) == true
@test hybridalphasat(FiniteIndexTruth(2), ∧(FiniteIndexTruth(1), parseformula("p")), IG4) == true
@test hybridalphasat(FiniteIndexTruth(3), ∧(FiniteIndexTruth(2), parseformula("p")), IG4) == false
@test hybridalphasat(FiniteIndexTruth(3), ∧(FiniteIndexTruth(3), parseformula("p")), IG4) == true
@test hybridalphasat(FiniteIndexTruth(3), ∧(FiniteIndexTruth(4), parseformula("p")), IG4) == true
@test hybridalphasat(FiniteIndexTruth(3), ∧(FiniteIndexTruth(1), parseformula("p")), IG4) == true
@test hybridalphasat(FiniteIndexTruth(4), ∧(FiniteIndexTruth(2), parseformula("p")), IG4) == false
@test hybridalphasat(FiniteIndexTruth(4), ∧(FiniteIndexTruth(3), parseformula("p")), IG4) == false
@test hybridalphasat(FiniteIndexTruth(4), ∧(FiniteIndexTruth(4), parseformula("p")), IG4) == true
@test hybridalphasat(FiniteIndexTruth(4), ∧(FiniteIndexTruth(1), parseformula("p")), IG4) == true
@test hybridalphasat(FiniteIndexTruth(1), ∧(FiniteIndexTruth(2), parseformula("p")), IG4) == false
@test hybridalphasat(FiniteIndexTruth(1), ∧(FiniteIndexTruth(3), parseformula("p")), IG4) == false
@test hybridalphasat(FiniteIndexTruth(1), ∧(FiniteIndexTruth(4), parseformula("p")), IG4) == false
@test hybridalphasat(FiniteIndexTruth(1), ∧(FiniteIndexTruth(1), parseformula("p")), IG4) == true

@test hybridalphasat(FiniteIndexTruth(2), ∧(parseformula("p"), parseformula("p")), IG4) == true
@test hybridalphasat(FiniteIndexTruth(3), ∧(parseformula("p"), parseformula("p")), IG4) == true
@test hybridalphasat(FiniteIndexTruth(4), ∧(parseformula("p"), parseformula("p")), IG4) == true
@test hybridalphasat(FiniteIndexTruth(1), ∧(parseformula("p"), parseformula("p")), IG4) == true

@test hybridalphasat(FiniteIndexTruth(2), ∧(parseformula("p"), parseformula("q")), IG4) == true
@test hybridalphasat(FiniteIndexTruth(3), ∧(parseformula("p"), parseformula("q")), IG4) == true
@test hybridalphasat(FiniteIndexTruth(4), ∧(parseformula("p"), parseformula("q")), IG4) == true
@test hybridalphasat(FiniteIndexTruth(1), ∧(parseformula("p"), parseformula("q")), IG4) == true

@test hybridalphasat(FiniteIndexTruth(2), ∧(parseformula("q"), parseformula("p")), IG4) == true
@test hybridalphasat(FiniteIndexTruth(3), ∧(parseformula("q"), parseformula("p")), IG4) == true
@test hybridalphasat(FiniteIndexTruth(4), ∧(parseformula("q"), parseformula("p")), IG4) == true
@test hybridalphasat(FiniteIndexTruth(1), ∧(parseformula("q"), parseformula("p")), IG4) == true

############################################################################################
## Implication #############################################################################
############################################################################################

@test hybridalphasat(FiniteIndexTruth(2), →(FiniteIndexTruth(2), FiniteIndexTruth(2)), IG4) == true
@test hybridalphasat(FiniteIndexTruth(2), →(FiniteIndexTruth(2), FiniteIndexTruth(3)), IG4) == true
@test hybridalphasat(FiniteIndexTruth(2), →(FiniteIndexTruth(2), FiniteIndexTruth(4)), IG4) == true
@test hybridalphasat(FiniteIndexTruth(2), →(FiniteIndexTruth(2), FiniteIndexTruth(1)), IG4) == true
@test hybridalphasat(FiniteIndexTruth(2), →(FiniteIndexTruth(3), FiniteIndexTruth(2)), IG4) == true
@test hybridalphasat(FiniteIndexTruth(2), →(FiniteIndexTruth(3), FiniteIndexTruth(3)), IG4) == true
@test hybridalphasat(FiniteIndexTruth(2), →(FiniteIndexTruth(3), FiniteIndexTruth(4)), IG4) == true
@test hybridalphasat(FiniteIndexTruth(2), →(FiniteIndexTruth(3), FiniteIndexTruth(1)), IG4) == true
@test hybridalphasat(FiniteIndexTruth(2), →(FiniteIndexTruth(4), FiniteIndexTruth(2)), IG4) == true
@test hybridalphasat(FiniteIndexTruth(2), →(FiniteIndexTruth(4), FiniteIndexTruth(3)), IG4) == true
@test hybridalphasat(FiniteIndexTruth(2), →(FiniteIndexTruth(4), FiniteIndexTruth(4)), IG4) == true
@test hybridalphasat(FiniteIndexTruth(2), →(FiniteIndexTruth(4), FiniteIndexTruth(1)), IG4) == true
@test hybridalphasat(FiniteIndexTruth(2), →(FiniteIndexTruth(1), FiniteIndexTruth(2)), IG4) == true
@test hybridalphasat(FiniteIndexTruth(2), →(FiniteIndexTruth(1), FiniteIndexTruth(3)), IG4) == true
@test hybridalphasat(FiniteIndexTruth(2), →(FiniteIndexTruth(1), FiniteIndexTruth(4)), IG4) == true
@test hybridalphasat(FiniteIndexTruth(2), →(FiniteIndexTruth(1), FiniteIndexTruth(1)), IG4) == true

@test hybridalphasat(FiniteIndexTruth(3), →(FiniteIndexTruth(2), FiniteIndexTruth(2)), IG4) == true
@test hybridalphasat(FiniteIndexTruth(3), →(FiniteIndexTruth(2), FiniteIndexTruth(3)), IG4) == true
@test hybridalphasat(FiniteIndexTruth(3), →(FiniteIndexTruth(2), FiniteIndexTruth(4)), IG4) == true
@test hybridalphasat(FiniteIndexTruth(3), →(FiniteIndexTruth(2), FiniteIndexTruth(1)), IG4) == true
@test hybridalphasat(FiniteIndexTruth(3), →(FiniteIndexTruth(3), FiniteIndexTruth(2)), IG4) == false
@test hybridalphasat(FiniteIndexTruth(3), →(FiniteIndexTruth(3), FiniteIndexTruth(3)), IG4) == true
@test hybridalphasat(FiniteIndexTruth(3), →(FiniteIndexTruth(3), FiniteIndexTruth(4)), IG4) == true
@test hybridalphasat(FiniteIndexTruth(3), →(FiniteIndexTruth(3), FiniteIndexTruth(1)), IG4) == true
@test hybridalphasat(FiniteIndexTruth(3), →(FiniteIndexTruth(4), FiniteIndexTruth(2)), IG4) == false
@test hybridalphasat(FiniteIndexTruth(3), →(FiniteIndexTruth(4), FiniteIndexTruth(3)), IG4) == true
@test hybridalphasat(FiniteIndexTruth(3), →(FiniteIndexTruth(4), FiniteIndexTruth(4)), IG4) == true
@test hybridalphasat(FiniteIndexTruth(3), →(FiniteIndexTruth(4), FiniteIndexTruth(1)), IG4) == true
@test hybridalphasat(FiniteIndexTruth(3), →(FiniteIndexTruth(1), FiniteIndexTruth(2)), IG4) == false
@test hybridalphasat(FiniteIndexTruth(3), →(FiniteIndexTruth(1), FiniteIndexTruth(3)), IG4) == true
@test hybridalphasat(FiniteIndexTruth(3), →(FiniteIndexTruth(1), FiniteIndexTruth(4)), IG4) == true
@test hybridalphasat(FiniteIndexTruth(3), →(FiniteIndexTruth(1), FiniteIndexTruth(1)), IG4) == true

@test hybridalphasat(FiniteIndexTruth(4), →(FiniteIndexTruth(2), FiniteIndexTruth(2)), IG4) == true
@test hybridalphasat(FiniteIndexTruth(4), →(FiniteIndexTruth(2), FiniteIndexTruth(3)), IG4) == true
@test hybridalphasat(FiniteIndexTruth(4), →(FiniteIndexTruth(2), FiniteIndexTruth(4)), IG4) == true
@test hybridalphasat(FiniteIndexTruth(4), →(FiniteIndexTruth(2), FiniteIndexTruth(1)), IG4) == true
@test hybridalphasat(FiniteIndexTruth(4), →(FiniteIndexTruth(3), FiniteIndexTruth(2)), IG4) == false
@test hybridalphasat(FiniteIndexTruth(4), →(FiniteIndexTruth(3), FiniteIndexTruth(3)), IG4) == true
@test hybridalphasat(FiniteIndexTruth(4), →(FiniteIndexTruth(3), FiniteIndexTruth(4)), IG4) == true
@test hybridalphasat(FiniteIndexTruth(4), →(FiniteIndexTruth(3), FiniteIndexTruth(1)), IG4) == true
@test hybridalphasat(FiniteIndexTruth(4), →(FiniteIndexTruth(4), FiniteIndexTruth(2)), IG4) == false
@test hybridalphasat(FiniteIndexTruth(4), →(FiniteIndexTruth(4), FiniteIndexTruth(3)), IG4) == false
@test hybridalphasat(FiniteIndexTruth(4), →(FiniteIndexTruth(4), FiniteIndexTruth(4)), IG4) == true
@test hybridalphasat(FiniteIndexTruth(4), →(FiniteIndexTruth(4), FiniteIndexTruth(1)), IG4) == true
@test hybridalphasat(FiniteIndexTruth(4), →(FiniteIndexTruth(1), FiniteIndexTruth(2)), IG4) == false
@test hybridalphasat(FiniteIndexTruth(4), →(FiniteIndexTruth(1), FiniteIndexTruth(3)), IG4) == false
@test hybridalphasat(FiniteIndexTruth(4), →(FiniteIndexTruth(1), FiniteIndexTruth(4)), IG4) == true
@test hybridalphasat(FiniteIndexTruth(4), →(FiniteIndexTruth(1), FiniteIndexTruth(1)), IG4) == true

@test hybridalphasat(FiniteIndexTruth(1), →(FiniteIndexTruth(2), FiniteIndexTruth(2)), IG4) == true
@test hybridalphasat(FiniteIndexTruth(1), →(FiniteIndexTruth(2), FiniteIndexTruth(3)), IG4) == true
@test hybridalphasat(FiniteIndexTruth(1), →(FiniteIndexTruth(2), FiniteIndexTruth(4)), IG4) == true
@test hybridalphasat(FiniteIndexTruth(1), →(FiniteIndexTruth(2), FiniteIndexTruth(1)), IG4) == true
@test hybridalphasat(FiniteIndexTruth(1), →(FiniteIndexTruth(3), FiniteIndexTruth(2)), IG4) == false
@test hybridalphasat(FiniteIndexTruth(1), →(FiniteIndexTruth(3), FiniteIndexTruth(3)), IG4) == true
@test hybridalphasat(FiniteIndexTruth(1), →(FiniteIndexTruth(3), FiniteIndexTruth(4)), IG4) == true
@test hybridalphasat(FiniteIndexTruth(1), →(FiniteIndexTruth(3), FiniteIndexTruth(1)), IG4) == true
@test hybridalphasat(FiniteIndexTruth(1), →(FiniteIndexTruth(4), FiniteIndexTruth(2)), IG4) == false
@test hybridalphasat(FiniteIndexTruth(1), →(FiniteIndexTruth(4), FiniteIndexTruth(3)), IG4) == false
@test hybridalphasat(FiniteIndexTruth(1), →(FiniteIndexTruth(4), FiniteIndexTruth(4)), IG4) == true
@test hybridalphasat(FiniteIndexTruth(1), →(FiniteIndexTruth(4), FiniteIndexTruth(1)), IG4) == true
@test hybridalphasat(FiniteIndexTruth(1), →(FiniteIndexTruth(1), FiniteIndexTruth(2)), IG4) == false
@test hybridalphasat(FiniteIndexTruth(1), →(FiniteIndexTruth(1), FiniteIndexTruth(3)), IG4) == false
@test hybridalphasat(FiniteIndexTruth(1), →(FiniteIndexTruth(1), FiniteIndexTruth(4)), IG4) == false
@test hybridalphasat(FiniteIndexTruth(1), →(FiniteIndexTruth(1), FiniteIndexTruth(1)), IG4) == true

@test hybridalphasat(FiniteIndexTruth(2), →(parseformula("p"), FiniteIndexTruth(2)), IG4) == true
@test hybridalphasat(FiniteIndexTruth(2), →(parseformula("p"), FiniteIndexTruth(3)), IG4) == true
@test hybridalphasat(FiniteIndexTruth(2), →(parseformula("p"), FiniteIndexTruth(4)), IG4) == true
@test hybridalphasat(FiniteIndexTruth(2), →(parseformula("p"), FiniteIndexTruth(1)), IG4) == true
@test hybridalphasat(FiniteIndexTruth(3), →(parseformula("p"), FiniteIndexTruth(2)), IG4) == true
@test hybridalphasat(FiniteIndexTruth(3), →(parseformula("p"), FiniteIndexTruth(3)), IG4) == true
@test hybridalphasat(FiniteIndexTruth(3), →(parseformula("p"), FiniteIndexTruth(4)), IG4) == true
@test hybridalphasat(FiniteIndexTruth(3), →(parseformula("p"), FiniteIndexTruth(1)), IG4) == true
@test hybridalphasat(FiniteIndexTruth(4), →(parseformula("p"), FiniteIndexTruth(2)), IG4) == true
@test hybridalphasat(FiniteIndexTruth(4), →(parseformula("p"), FiniteIndexTruth(3)), IG4) == true
@test hybridalphasat(FiniteIndexTruth(4), →(parseformula("p"), FiniteIndexTruth(4)), IG4) == true
@test hybridalphasat(FiniteIndexTruth(4), →(parseformula("p"), FiniteIndexTruth(1)), IG4) == true
@test hybridalphasat(FiniteIndexTruth(1), →(parseformula("p"), FiniteIndexTruth(2)), IG4) == true
@test hybridalphasat(FiniteIndexTruth(1), →(parseformula("p"), FiniteIndexTruth(3)), IG4) == true
@test hybridalphasat(FiniteIndexTruth(1), →(parseformula("p"), FiniteIndexTruth(4)), IG4) == true
@test hybridalphasat(FiniteIndexTruth(1), →(parseformula("p"), FiniteIndexTruth(1)), IG4) == true

@test hybridalphasat(FiniteIndexTruth(2), →(FiniteIndexTruth(2), parseformula("p")), IG4) == true
@test hybridalphasat(FiniteIndexTruth(2), →(FiniteIndexTruth(3), parseformula("p")), IG4) == true
@test hybridalphasat(FiniteIndexTruth(2), →(FiniteIndexTruth(4), parseformula("p")), IG4) == true
@test hybridalphasat(FiniteIndexTruth(2), →(FiniteIndexTruth(1), parseformula("p")), IG4) == true
@test hybridalphasat(FiniteIndexTruth(3), →(FiniteIndexTruth(2), parseformula("p")), IG4) == true
@test hybridalphasat(FiniteIndexTruth(3), →(FiniteIndexTruth(3), parseformula("p")), IG4) == true
@test hybridalphasat(FiniteIndexTruth(3), →(FiniteIndexTruth(4), parseformula("p")), IG4) == true
@test hybridalphasat(FiniteIndexTruth(3), →(FiniteIndexTruth(1), parseformula("p")), IG4) == true
@test hybridalphasat(FiniteIndexTruth(4), →(FiniteIndexTruth(2), parseformula("p")), IG4) == true
@test hybridalphasat(FiniteIndexTruth(4), →(FiniteIndexTruth(3), parseformula("p")), IG4) == true
@test hybridalphasat(FiniteIndexTruth(4), →(FiniteIndexTruth(4), parseformula("p")), IG4) == true
@test hybridalphasat(FiniteIndexTruth(4), →(FiniteIndexTruth(1), parseformula("p")), IG4) == true
@test hybridalphasat(FiniteIndexTruth(1), →(FiniteIndexTruth(2), parseformula("p")), IG4) == true
@test hybridalphasat(FiniteIndexTruth(1), →(FiniteIndexTruth(3), parseformula("p")), IG4) == true
@test hybridalphasat(FiniteIndexTruth(1), →(FiniteIndexTruth(4), parseformula("p")), IG4) == true
@test hybridalphasat(FiniteIndexTruth(1), →(FiniteIndexTruth(1), parseformula("p")), IG4) == true

@test hybridalphasat(FiniteIndexTruth(2), →(parseformula("p"), parseformula("p")), IG4) == true
@test hybridalphasat(FiniteIndexTruth(3), →(parseformula("p"), parseformula("p")), IG4) == true
@test hybridalphasat(FiniteIndexTruth(4), →(parseformula("p"), parseformula("p")), IG4) == true
@test hybridalphasat(FiniteIndexTruth(1), →(parseformula("p"), parseformula("p")), IG4) == true

@test hybridalphasat(FiniteIndexTruth(2), →(parseformula("p"), parseformula("q")), IG4) == true
@test hybridalphasat(FiniteIndexTruth(3), →(parseformula("p"), parseformula("q")), IG4) == true
@test hybridalphasat(FiniteIndexTruth(4), →(parseformula("p"), parseformula("q")), IG4) == true
@test hybridalphasat(FiniteIndexTruth(1), →(parseformula("p"), parseformula("q")), IG4) == true

@test hybridalphasat(FiniteIndexTruth(2), →(parseformula("q"), parseformula("p")), IG4) == true
@test hybridalphasat(FiniteIndexTruth(3), →(parseformula("q"), parseformula("p")), IG4) == true
@test hybridalphasat(FiniteIndexTruth(4), →(parseformula("q"), parseformula("p")), IG4) == true
@test hybridalphasat(FiniteIndexTruth(1), →(parseformula("q"), parseformula("p")), IG4) == true

###########################################################################################
### IŁ4 ####################################################################################
###########################################################################################

using SoleLogics.ManyValuedLogics: Ł4

IŁ4 = convert(FiniteIndexFLewAlgebra, Ł4)

############################################################################################
## Base cases ##############################################################################
############################################################################################

@test hybridalphasat(FiniteIndexTruth(2), FiniteIndexTruth(2), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(2), FiniteIndexTruth(3), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(2), FiniteIndexTruth(4), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(2), FiniteIndexTruth(1), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(3), FiniteIndexTruth(2), IŁ4) == false
@test hybridalphasat(FiniteIndexTruth(3), FiniteIndexTruth(3), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(3), FiniteIndexTruth(4), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(3), FiniteIndexTruth(1), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(4), FiniteIndexTruth(2), IŁ4) == false
@test hybridalphasat(FiniteIndexTruth(4), FiniteIndexTruth(3), IŁ4) == false
@test hybridalphasat(FiniteIndexTruth(4), FiniteIndexTruth(4), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(4), FiniteIndexTruth(1), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(1), FiniteIndexTruth(2), IŁ4) == false
@test hybridalphasat(FiniteIndexTruth(1), FiniteIndexTruth(3), IŁ4) == false
@test hybridalphasat(FiniteIndexTruth(1), FiniteIndexTruth(4), IŁ4) == false
@test hybridalphasat(FiniteIndexTruth(1), FiniteIndexTruth(1), IŁ4) == true

@test hybridalphasat(FiniteIndexTruth(2), parseformula("p"), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(3), parseformula("p"), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(4), parseformula("p"), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(1), parseformula("p"), IŁ4) == true

############################################################################################
## (Strong) disjuction #####################################################################
############################################################################################

@test hybridalphasat(FiniteIndexTruth(2), ∨(FiniteIndexTruth(2), FiniteIndexTruth(2)), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(2), ∨(FiniteIndexTruth(2), FiniteIndexTruth(3)), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(2), ∨(FiniteIndexTruth(2), FiniteIndexTruth(4)), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(2), ∨(FiniteIndexTruth(2), FiniteIndexTruth(1)), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(2), ∨(FiniteIndexTruth(3), FiniteIndexTruth(2)), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(2), ∨(FiniteIndexTruth(3), FiniteIndexTruth(3)), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(2), ∨(FiniteIndexTruth(3), FiniteIndexTruth(4)), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(2), ∨(FiniteIndexTruth(3), FiniteIndexTruth(1)), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(2), ∨(FiniteIndexTruth(4), FiniteIndexTruth(2)), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(2), ∨(FiniteIndexTruth(4), FiniteIndexTruth(3)), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(2), ∨(FiniteIndexTruth(4), FiniteIndexTruth(4)), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(2), ∨(FiniteIndexTruth(4), FiniteIndexTruth(1)), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(2), ∨(FiniteIndexTruth(1), FiniteIndexTruth(2)), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(2), ∨(FiniteIndexTruth(1), FiniteIndexTruth(3)), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(2), ∨(FiniteIndexTruth(1), FiniteIndexTruth(4)), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(2), ∨(FiniteIndexTruth(1), FiniteIndexTruth(1)), IŁ4) == true

@test hybridalphasat(FiniteIndexTruth(3), ∨(FiniteIndexTruth(2), FiniteIndexTruth(2)), IŁ4) == false
@test hybridalphasat(FiniteIndexTruth(3), ∨(FiniteIndexTruth(2), FiniteIndexTruth(3)), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(3), ∨(FiniteIndexTruth(2), FiniteIndexTruth(4)), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(3), ∨(FiniteIndexTruth(2), FiniteIndexTruth(1)), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(3), ∨(FiniteIndexTruth(3), FiniteIndexTruth(2)), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(3), ∨(FiniteIndexTruth(3), FiniteIndexTruth(3)), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(3), ∨(FiniteIndexTruth(3), FiniteIndexTruth(4)), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(3), ∨(FiniteIndexTruth(3), FiniteIndexTruth(1)), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(3), ∨(FiniteIndexTruth(4), FiniteIndexTruth(2)), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(3), ∨(FiniteIndexTruth(4), FiniteIndexTruth(3)), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(3), ∨(FiniteIndexTruth(4), FiniteIndexTruth(4)), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(3), ∨(FiniteIndexTruth(4), FiniteIndexTruth(1)), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(3), ∨(FiniteIndexTruth(1), FiniteIndexTruth(2)), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(3), ∨(FiniteIndexTruth(1), FiniteIndexTruth(3)), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(3), ∨(FiniteIndexTruth(1), FiniteIndexTruth(4)), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(3), ∨(FiniteIndexTruth(1), FiniteIndexTruth(1)), IŁ4) == true

@test hybridalphasat(FiniteIndexTruth(4), ∨(FiniteIndexTruth(2), FiniteIndexTruth(2)), IŁ4) == false
@test hybridalphasat(FiniteIndexTruth(4), ∨(FiniteIndexTruth(2), FiniteIndexTruth(3)), IŁ4) == false
@test hybridalphasat(FiniteIndexTruth(4), ∨(FiniteIndexTruth(2), FiniteIndexTruth(4)), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(4), ∨(FiniteIndexTruth(2), FiniteIndexTruth(1)), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(4), ∨(FiniteIndexTruth(3), FiniteIndexTruth(2)), IŁ4) == false
@test hybridalphasat(FiniteIndexTruth(4), ∨(FiniteIndexTruth(3), FiniteIndexTruth(3)), IŁ4) == false
@test hybridalphasat(FiniteIndexTruth(4), ∨(FiniteIndexTruth(3), FiniteIndexTruth(4)), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(4), ∨(FiniteIndexTruth(3), FiniteIndexTruth(1)), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(4), ∨(FiniteIndexTruth(4), FiniteIndexTruth(2)), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(4), ∨(FiniteIndexTruth(4), FiniteIndexTruth(3)), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(4), ∨(FiniteIndexTruth(4), FiniteIndexTruth(4)), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(4), ∨(FiniteIndexTruth(4), FiniteIndexTruth(1)), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(4), ∨(FiniteIndexTruth(1), FiniteIndexTruth(2)), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(4), ∨(FiniteIndexTruth(1), FiniteIndexTruth(3)), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(4), ∨(FiniteIndexTruth(1), FiniteIndexTruth(4)), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(4), ∨(FiniteIndexTruth(1), FiniteIndexTruth(1)), IŁ4) == true

@test hybridalphasat(FiniteIndexTruth(1), ∨(FiniteIndexTruth(2), FiniteIndexTruth(2)), IŁ4) == false
@test hybridalphasat(FiniteIndexTruth(1), ∨(FiniteIndexTruth(2), FiniteIndexTruth(3)), IŁ4) == false
@test hybridalphasat(FiniteIndexTruth(1), ∨(FiniteIndexTruth(2), FiniteIndexTruth(4)), IŁ4) == false
@test hybridalphasat(FiniteIndexTruth(1), ∨(FiniteIndexTruth(2), FiniteIndexTruth(1)), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(1), ∨(FiniteIndexTruth(3), FiniteIndexTruth(2)), IŁ4) == false
@test hybridalphasat(FiniteIndexTruth(1), ∨(FiniteIndexTruth(3), FiniteIndexTruth(3)), IŁ4) == false
@test hybridalphasat(FiniteIndexTruth(1), ∨(FiniteIndexTruth(3), FiniteIndexTruth(4)), IŁ4) == false
@test hybridalphasat(FiniteIndexTruth(1), ∨(FiniteIndexTruth(3), FiniteIndexTruth(1)), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(1), ∨(FiniteIndexTruth(4), FiniteIndexTruth(2)), IŁ4) == false
@test hybridalphasat(FiniteIndexTruth(1), ∨(FiniteIndexTruth(4), FiniteIndexTruth(3)), IŁ4) == false
@test hybridalphasat(FiniteIndexTruth(1), ∨(FiniteIndexTruth(4), FiniteIndexTruth(4)), IŁ4) == false
@test hybridalphasat(FiniteIndexTruth(1), ∨(FiniteIndexTruth(4), FiniteIndexTruth(1)), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(1), ∨(FiniteIndexTruth(1), FiniteIndexTruth(2)), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(1), ∨(FiniteIndexTruth(1), FiniteIndexTruth(3)), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(1), ∨(FiniteIndexTruth(1), FiniteIndexTruth(4)), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(1), ∨(FiniteIndexTruth(1), FiniteIndexTruth(1)), IŁ4) == true

@test hybridalphasat(FiniteIndexTruth(2), ∨(parseformula("p"), FiniteIndexTruth(2)), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(2), ∨(parseformula("p"), FiniteIndexTruth(3)), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(2), ∨(parseformula("p"), FiniteIndexTruth(4)), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(2), ∨(parseformula("p"), FiniteIndexTruth(1)), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(3), ∨(parseformula("p"), FiniteIndexTruth(2)), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(3), ∨(parseformula("p"), FiniteIndexTruth(3)), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(3), ∨(parseformula("p"), FiniteIndexTruth(4)), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(3), ∨(parseformula("p"), FiniteIndexTruth(1)), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(4), ∨(parseformula("p"), FiniteIndexTruth(2)), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(4), ∨(parseformula("p"), FiniteIndexTruth(3)), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(4), ∨(parseformula("p"), FiniteIndexTruth(4)), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(4), ∨(parseformula("p"), FiniteIndexTruth(1)), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(1), ∨(parseformula("p"), FiniteIndexTruth(2)), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(1), ∨(parseformula("p"), FiniteIndexTruth(3)), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(1), ∨(parseformula("p"), FiniteIndexTruth(4)), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(1), ∨(parseformula("p"), FiniteIndexTruth(1)), IŁ4) == true

@test hybridalphasat(FiniteIndexTruth(2), ∨(FiniteIndexTruth(2), parseformula("p")), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(2), ∨(FiniteIndexTruth(3), parseformula("p")), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(2), ∨(FiniteIndexTruth(4), parseformula("p")), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(2), ∨(FiniteIndexTruth(1), parseformula("p")), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(3), ∨(FiniteIndexTruth(2), parseformula("p")), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(3), ∨(FiniteIndexTruth(3), parseformula("p")), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(3), ∨(FiniteIndexTruth(4), parseformula("p")), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(3), ∨(FiniteIndexTruth(1), parseformula("p")), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(4), ∨(FiniteIndexTruth(2), parseformula("p")), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(4), ∨(FiniteIndexTruth(3), parseformula("p")), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(4), ∨(FiniteIndexTruth(4), parseformula("p")), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(4), ∨(FiniteIndexTruth(1), parseformula("p")), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(1), ∨(FiniteIndexTruth(2), parseformula("p")), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(1), ∨(FiniteIndexTruth(3), parseformula("p")), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(1), ∨(FiniteIndexTruth(4), parseformula("p")), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(1), ∨(FiniteIndexTruth(1), parseformula("p")), IŁ4) == true

@test hybridalphasat(FiniteIndexTruth(2), ∨(parseformula("p"), parseformula("p")), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(3), ∨(parseformula("p"), parseformula("p")), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(4), ∨(parseformula("p"), parseformula("p")), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(1), ∨(parseformula("p"), parseformula("p")), IŁ4) == true

@test hybridalphasat(FiniteIndexTruth(2), ∨(parseformula("p"), parseformula("q")), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(3), ∨(parseformula("p"), parseformula("q")), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(4), ∨(parseformula("p"), parseformula("q")), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(1), ∨(parseformula("p"), parseformula("q")), IŁ4) == true

@test hybridalphasat(FiniteIndexTruth(2), ∨(parseformula("q"), parseformula("q")), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(3), ∨(parseformula("q"), parseformula("q")), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(4), ∨(parseformula("q"), parseformula("q")), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(1), ∨(parseformula("q"), parseformula("q")), IŁ4) == true

############################################################################################
## (Strong) conjunction ####################################################################
############################################################################################

@test hybridalphasat(FiniteIndexTruth(2), ∧(FiniteIndexTruth(2), FiniteIndexTruth(2)), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(2), ∧(FiniteIndexTruth(2), FiniteIndexTruth(3)), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(2), ∧(FiniteIndexTruth(2), FiniteIndexTruth(4)), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(2), ∧(FiniteIndexTruth(2), FiniteIndexTruth(1)), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(2), ∧(FiniteIndexTruth(3), FiniteIndexTruth(2)), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(2), ∧(FiniteIndexTruth(3), FiniteIndexTruth(3)), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(2), ∧(FiniteIndexTruth(3), FiniteIndexTruth(4)), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(2), ∧(FiniteIndexTruth(3), FiniteIndexTruth(1)), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(2), ∧(FiniteIndexTruth(4), FiniteIndexTruth(2)), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(2), ∧(FiniteIndexTruth(4), FiniteIndexTruth(3)), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(2), ∧(FiniteIndexTruth(4), FiniteIndexTruth(4)), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(2), ∧(FiniteIndexTruth(4), FiniteIndexTruth(1)), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(2), ∧(FiniteIndexTruth(1), FiniteIndexTruth(2)), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(2), ∧(FiniteIndexTruth(1), FiniteIndexTruth(3)), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(2), ∧(FiniteIndexTruth(1), FiniteIndexTruth(4)), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(2), ∧(FiniteIndexTruth(1), FiniteIndexTruth(1)), IŁ4) == true

@test hybridalphasat(FiniteIndexTruth(3), ∧(FiniteIndexTruth(2), FiniteIndexTruth(2)), IŁ4) == false
@test hybridalphasat(FiniteIndexTruth(3), ∧(FiniteIndexTruth(2), FiniteIndexTruth(3)), IŁ4) == false
@test hybridalphasat(FiniteIndexTruth(3), ∧(FiniteIndexTruth(2), FiniteIndexTruth(4)), IŁ4) == false
@test hybridalphasat(FiniteIndexTruth(3), ∧(FiniteIndexTruth(2), FiniteIndexTruth(1)), IŁ4) == false
@test hybridalphasat(FiniteIndexTruth(3), ∧(FiniteIndexTruth(3), FiniteIndexTruth(2)), IŁ4) == false
@test hybridalphasat(FiniteIndexTruth(3), ∧(FiniteIndexTruth(3), FiniteIndexTruth(3)), IŁ4) == false
@test hybridalphasat(FiniteIndexTruth(3), ∧(FiniteIndexTruth(3), FiniteIndexTruth(4)), IŁ4) == false
@test hybridalphasat(FiniteIndexTruth(3), ∧(FiniteIndexTruth(3), FiniteIndexTruth(1)), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(3), ∧(FiniteIndexTruth(4), FiniteIndexTruth(2)), IŁ4) == false
@test hybridalphasat(FiniteIndexTruth(3), ∧(FiniteIndexTruth(4), FiniteIndexTruth(3)), IŁ4) == false
@test hybridalphasat(FiniteIndexTruth(3), ∧(FiniteIndexTruth(4), FiniteIndexTruth(4)), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(3), ∧(FiniteIndexTruth(4), FiniteIndexTruth(1)), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(3), ∧(FiniteIndexTruth(1), FiniteIndexTruth(2)), IŁ4) == false
@test hybridalphasat(FiniteIndexTruth(3), ∧(FiniteIndexTruth(1), FiniteIndexTruth(3)), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(3), ∧(FiniteIndexTruth(1), FiniteIndexTruth(4)), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(3), ∧(FiniteIndexTruth(1), FiniteIndexTruth(1)), IŁ4) == true

@test hybridalphasat(FiniteIndexTruth(4), ∧(FiniteIndexTruth(2), FiniteIndexTruth(2)), IŁ4) == false
@test hybridalphasat(FiniteIndexTruth(4), ∧(FiniteIndexTruth(2), FiniteIndexTruth(3)), IŁ4) == false
@test hybridalphasat(FiniteIndexTruth(4), ∧(FiniteIndexTruth(2), FiniteIndexTruth(4)), IŁ4) == false
@test hybridalphasat(FiniteIndexTruth(4), ∧(FiniteIndexTruth(2), FiniteIndexTruth(1)), IŁ4) == false
@test hybridalphasat(FiniteIndexTruth(4), ∧(FiniteIndexTruth(3), FiniteIndexTruth(2)), IŁ4) == false
@test hybridalphasat(FiniteIndexTruth(4), ∧(FiniteIndexTruth(3), FiniteIndexTruth(3)), IŁ4) == false
@test hybridalphasat(FiniteIndexTruth(4), ∧(FiniteIndexTruth(3), FiniteIndexTruth(4)), IŁ4) == false
@test hybridalphasat(FiniteIndexTruth(4), ∧(FiniteIndexTruth(3), FiniteIndexTruth(1)), IŁ4) == false
@test hybridalphasat(FiniteIndexTruth(4), ∧(FiniteIndexTruth(4), FiniteIndexTruth(2)), IŁ4) == false
@test hybridalphasat(FiniteIndexTruth(4), ∧(FiniteIndexTruth(4), FiniteIndexTruth(3)), IŁ4) == false
@test hybridalphasat(FiniteIndexTruth(4), ∧(FiniteIndexTruth(4), FiniteIndexTruth(4)), IŁ4) == false
@test hybridalphasat(FiniteIndexTruth(4), ∧(FiniteIndexTruth(4), FiniteIndexTruth(1)), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(4), ∧(FiniteIndexTruth(1), FiniteIndexTruth(2)), IŁ4) == false
@test hybridalphasat(FiniteIndexTruth(4), ∧(FiniteIndexTruth(1), FiniteIndexTruth(3)), IŁ4) == false
@test hybridalphasat(FiniteIndexTruth(4), ∧(FiniteIndexTruth(1), FiniteIndexTruth(4)), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(4), ∧(FiniteIndexTruth(1), FiniteIndexTruth(1)), IŁ4) == true

@test hybridalphasat(FiniteIndexTruth(1), ∧(FiniteIndexTruth(2), FiniteIndexTruth(2)), IŁ4) == false
@test hybridalphasat(FiniteIndexTruth(1), ∧(FiniteIndexTruth(2), FiniteIndexTruth(3)), IŁ4) == false
@test hybridalphasat(FiniteIndexTruth(1), ∧(FiniteIndexTruth(2), FiniteIndexTruth(4)), IŁ4) == false
@test hybridalphasat(FiniteIndexTruth(1), ∧(FiniteIndexTruth(2), FiniteIndexTruth(1)), IŁ4) == false
@test hybridalphasat(FiniteIndexTruth(1), ∧(FiniteIndexTruth(3), FiniteIndexTruth(2)), IŁ4) == false
@test hybridalphasat(FiniteIndexTruth(1), ∧(FiniteIndexTruth(3), FiniteIndexTruth(3)), IŁ4) == false
@test hybridalphasat(FiniteIndexTruth(1), ∧(FiniteIndexTruth(3), FiniteIndexTruth(4)), IŁ4) == false
@test hybridalphasat(FiniteIndexTruth(1), ∧(FiniteIndexTruth(3), FiniteIndexTruth(1)), IŁ4) == false
@test hybridalphasat(FiniteIndexTruth(1), ∧(FiniteIndexTruth(4), FiniteIndexTruth(2)), IŁ4) == false
@test hybridalphasat(FiniteIndexTruth(1), ∧(FiniteIndexTruth(4), FiniteIndexTruth(3)), IŁ4) == false
@test hybridalphasat(FiniteIndexTruth(1), ∧(FiniteIndexTruth(4), FiniteIndexTruth(4)), IŁ4) == false
@test hybridalphasat(FiniteIndexTruth(1), ∧(FiniteIndexTruth(4), FiniteIndexTruth(1)), IŁ4) == false
@test hybridalphasat(FiniteIndexTruth(1), ∧(FiniteIndexTruth(1), FiniteIndexTruth(2)), IŁ4) == false
@test hybridalphasat(FiniteIndexTruth(1), ∧(FiniteIndexTruth(1), FiniteIndexTruth(3)), IŁ4) == false
@test hybridalphasat(FiniteIndexTruth(1), ∧(FiniteIndexTruth(1), FiniteIndexTruth(4)), IŁ4) == false
@test hybridalphasat(FiniteIndexTruth(1), ∧(FiniteIndexTruth(1), FiniteIndexTruth(1)), IŁ4) == true

@test hybridalphasat(FiniteIndexTruth(2), ∧(parseformula("p"), FiniteIndexTruth(2)), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(2), ∧(parseformula("p"), FiniteIndexTruth(3)), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(2), ∧(parseformula("p"), FiniteIndexTruth(4)), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(2), ∧(parseformula("p"), FiniteIndexTruth(1)), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(3), ∧(parseformula("p"), FiniteIndexTruth(2)), IŁ4) == false
@test hybridalphasat(FiniteIndexTruth(3), ∧(parseformula("p"), FiniteIndexTruth(3)), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(3), ∧(parseformula("p"), FiniteIndexTruth(4)), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(3), ∧(parseformula("p"), FiniteIndexTruth(1)), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(4), ∧(parseformula("p"), FiniteIndexTruth(2)), IŁ4) == false
@test hybridalphasat(FiniteIndexTruth(4), ∧(parseformula("p"), FiniteIndexTruth(3)), IŁ4) == false
@test hybridalphasat(FiniteIndexTruth(4), ∧(parseformula("p"), FiniteIndexTruth(4)), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(4), ∧(parseformula("p"), FiniteIndexTruth(1)), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(1), ∧(parseformula("p"), FiniteIndexTruth(2)), IŁ4) == false
@test hybridalphasat(FiniteIndexTruth(1), ∧(parseformula("p"), FiniteIndexTruth(3)), IŁ4) == false
@test hybridalphasat(FiniteIndexTruth(1), ∧(parseformula("p"), FiniteIndexTruth(4)), IŁ4) == false
@test hybridalphasat(FiniteIndexTruth(1), ∧(parseformula("p"), FiniteIndexTruth(1)), IŁ4) == true

@test hybridalphasat(FiniteIndexTruth(2), ∧(FiniteIndexTruth(2), parseformula("p")), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(2), ∧(FiniteIndexTruth(3), parseformula("p")), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(2), ∧(FiniteIndexTruth(4), parseformula("p")), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(2), ∧(FiniteIndexTruth(1), parseformula("p")), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(3), ∧(FiniteIndexTruth(2), parseformula("p")), IŁ4) == false
@test hybridalphasat(FiniteIndexTruth(3), ∧(FiniteIndexTruth(3), parseformula("p")), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(3), ∧(FiniteIndexTruth(4), parseformula("p")), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(3), ∧(FiniteIndexTruth(1), parseformula("p")), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(4), ∧(FiniteIndexTruth(2), parseformula("p")), IŁ4) == false
@test hybridalphasat(FiniteIndexTruth(4), ∧(FiniteIndexTruth(3), parseformula("p")), IŁ4) == false
@test hybridalphasat(FiniteIndexTruth(4), ∧(FiniteIndexTruth(4), parseformula("p")), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(4), ∧(FiniteIndexTruth(1), parseformula("p")), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(1), ∧(FiniteIndexTruth(2), parseformula("p")), IŁ4) == false
@test hybridalphasat(FiniteIndexTruth(1), ∧(FiniteIndexTruth(3), parseformula("p")), IŁ4) == false
@test hybridalphasat(FiniteIndexTruth(1), ∧(FiniteIndexTruth(4), parseformula("p")), IŁ4) == false
@test hybridalphasat(FiniteIndexTruth(1), ∧(FiniteIndexTruth(1), parseformula("p")), IŁ4) == true

@test hybridalphasat(FiniteIndexTruth(2), ∧(parseformula("p"), parseformula("p")), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(3), ∧(parseformula("p"), parseformula("p")), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(4), ∧(parseformula("p"), parseformula("p")), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(1), ∧(parseformula("p"), parseformula("p")), IŁ4) == true

@test hybridalphasat(FiniteIndexTruth(2), ∧(parseformula("p"), parseformula("q")), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(3), ∧(parseformula("p"), parseformula("q")), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(4), ∧(parseformula("p"), parseformula("q")), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(1), ∧(parseformula("p"), parseformula("q")), IŁ4) == true

@test hybridalphasat(FiniteIndexTruth(2), ∧(parseformula("q"), parseformula("p")), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(3), ∧(parseformula("q"), parseformula("p")), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(4), ∧(parseformula("q"), parseformula("p")), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(1), ∧(parseformula("q"), parseformula("p")), IŁ4) == true

############################################################################################
## Implication #############################################################################
############################################################################################

@test hybridalphasat(FiniteIndexTruth(2), →(FiniteIndexTruth(2), FiniteIndexTruth(2)), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(2), →(FiniteIndexTruth(2), FiniteIndexTruth(3)), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(2), →(FiniteIndexTruth(2), FiniteIndexTruth(4)), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(2), →(FiniteIndexTruth(2), FiniteIndexTruth(1)), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(2), →(FiniteIndexTruth(3), FiniteIndexTruth(2)), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(2), →(FiniteIndexTruth(3), FiniteIndexTruth(3)), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(2), →(FiniteIndexTruth(3), FiniteIndexTruth(4)), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(2), →(FiniteIndexTruth(3), FiniteIndexTruth(1)), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(2), →(FiniteIndexTruth(4), FiniteIndexTruth(2)), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(2), →(FiniteIndexTruth(4), FiniteIndexTruth(3)), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(2), →(FiniteIndexTruth(4), FiniteIndexTruth(4)), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(2), →(FiniteIndexTruth(4), FiniteIndexTruth(1)), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(2), →(FiniteIndexTruth(1), FiniteIndexTruth(2)), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(2), →(FiniteIndexTruth(1), FiniteIndexTruth(3)), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(2), →(FiniteIndexTruth(1), FiniteIndexTruth(4)), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(2), →(FiniteIndexTruth(1), FiniteIndexTruth(1)), IŁ4) == true

@test hybridalphasat(FiniteIndexTruth(3), →(FiniteIndexTruth(2), FiniteIndexTruth(2)), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(3), →(FiniteIndexTruth(2), FiniteIndexTruth(3)), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(3), →(FiniteIndexTruth(2), FiniteIndexTruth(4)), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(3), →(FiniteIndexTruth(2), FiniteIndexTruth(1)), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(3), →(FiniteIndexTruth(3), FiniteIndexTruth(2)), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(3), →(FiniteIndexTruth(3), FiniteIndexTruth(3)), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(3), →(FiniteIndexTruth(3), FiniteIndexTruth(4)), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(3), →(FiniteIndexTruth(3), FiniteIndexTruth(1)), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(3), →(FiniteIndexTruth(4), FiniteIndexTruth(2)), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(3), →(FiniteIndexTruth(4), FiniteIndexTruth(3)), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(3), →(FiniteIndexTruth(4), FiniteIndexTruth(4)), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(3), →(FiniteIndexTruth(4), FiniteIndexTruth(1)), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(3), →(FiniteIndexTruth(1), FiniteIndexTruth(2)), IŁ4) == false
@test hybridalphasat(FiniteIndexTruth(3), →(FiniteIndexTruth(1), FiniteIndexTruth(3)), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(3), →(FiniteIndexTruth(1), FiniteIndexTruth(4)), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(3), →(FiniteIndexTruth(1), FiniteIndexTruth(1)), IŁ4) == true

@test hybridalphasat(FiniteIndexTruth(4), →(FiniteIndexTruth(2), FiniteIndexTruth(2)), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(4), →(FiniteIndexTruth(2), FiniteIndexTruth(3)), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(4), →(FiniteIndexTruth(2), FiniteIndexTruth(4)), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(4), →(FiniteIndexTruth(2), FiniteIndexTruth(1)), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(4), →(FiniteIndexTruth(3), FiniteIndexTruth(2)), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(4), →(FiniteIndexTruth(3), FiniteIndexTruth(3)), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(4), →(FiniteIndexTruth(3), FiniteIndexTruth(4)), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(4), →(FiniteIndexTruth(3), FiniteIndexTruth(1)), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(4), →(FiniteIndexTruth(4), FiniteIndexTruth(2)), IŁ4) == false
@test hybridalphasat(FiniteIndexTruth(4), →(FiniteIndexTruth(4), FiniteIndexTruth(3)), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(4), →(FiniteIndexTruth(4), FiniteIndexTruth(4)), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(4), →(FiniteIndexTruth(4), FiniteIndexTruth(1)), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(4), →(FiniteIndexTruth(1), FiniteIndexTruth(2)), IŁ4) == false
@test hybridalphasat(FiniteIndexTruth(4), →(FiniteIndexTruth(1), FiniteIndexTruth(3)), IŁ4) == false
@test hybridalphasat(FiniteIndexTruth(4), →(FiniteIndexTruth(1), FiniteIndexTruth(4)), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(4), →(FiniteIndexTruth(1), FiniteIndexTruth(1)), IŁ4) == true

@test hybridalphasat(FiniteIndexTruth(1), →(FiniteIndexTruth(2), FiniteIndexTruth(2)), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(1), →(FiniteIndexTruth(2), FiniteIndexTruth(3)), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(1), →(FiniteIndexTruth(2), FiniteIndexTruth(4)), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(1), →(FiniteIndexTruth(2), FiniteIndexTruth(1)), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(1), →(FiniteIndexTruth(3), FiniteIndexTruth(2)), IŁ4) == false
@test hybridalphasat(FiniteIndexTruth(1), →(FiniteIndexTruth(3), FiniteIndexTruth(3)), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(1), →(FiniteIndexTruth(3), FiniteIndexTruth(4)), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(1), →(FiniteIndexTruth(3), FiniteIndexTruth(1)), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(1), →(FiniteIndexTruth(4), FiniteIndexTruth(2)), IŁ4) == false
@test hybridalphasat(FiniteIndexTruth(1), →(FiniteIndexTruth(4), FiniteIndexTruth(3)), IŁ4) == false
@test hybridalphasat(FiniteIndexTruth(1), →(FiniteIndexTruth(4), FiniteIndexTruth(4)), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(1), →(FiniteIndexTruth(4), FiniteIndexTruth(1)), IŁ4) == true
@test hybridalphasat(FiniteIndexTruth(1), →(FiniteIndexTruth(1), FiniteIndexTruth(2)), IŁ4) == false
@test hybridalphasat(FiniteIndexTruth(1), →(FiniteIndexTruth(1), FiniteIndexTruth(3)), IŁ4) == false
@test hybridalphasat(FiniteIndexTruth(1), →(FiniteIndexTruth(1), FiniteIndexTruth(4)), IŁ4) == false
@test hybridalphasat(FiniteIndexTruth(1), →(FiniteIndexTruth(1), FiniteIndexTruth(1)), IŁ4) == true

@test hybridalphasat(FiniteIndexTruth(2), →(parseformula("p"), FiniteIndexTruth(2)), IG4) == true
@test hybridalphasat(FiniteIndexTruth(2), →(parseformula("p"), FiniteIndexTruth(3)), IG4) == true
@test hybridalphasat(FiniteIndexTruth(2), →(parseformula("p"), FiniteIndexTruth(4)), IG4) == true
@test hybridalphasat(FiniteIndexTruth(2), →(parseformula("p"), FiniteIndexTruth(1)), IG4) == true
@test hybridalphasat(FiniteIndexTruth(3), →(parseformula("p"), FiniteIndexTruth(2)), IG4) == true
@test hybridalphasat(FiniteIndexTruth(3), →(parseformula("p"), FiniteIndexTruth(3)), IG4) == true
@test hybridalphasat(FiniteIndexTruth(3), →(parseformula("p"), FiniteIndexTruth(4)), IG4) == true
@test hybridalphasat(FiniteIndexTruth(3), →(parseformula("p"), FiniteIndexTruth(1)), IG4) == true
@test hybridalphasat(FiniteIndexTruth(4), →(parseformula("p"), FiniteIndexTruth(2)), IG4) == true
@test hybridalphasat(FiniteIndexTruth(4), →(parseformula("p"), FiniteIndexTruth(3)), IG4) == true
@test hybridalphasat(FiniteIndexTruth(4), →(parseformula("p"), FiniteIndexTruth(4)), IG4) == true
@test hybridalphasat(FiniteIndexTruth(4), →(parseformula("p"), FiniteIndexTruth(1)), IG4) == true
@test hybridalphasat(FiniteIndexTruth(1), →(parseformula("p"), FiniteIndexTruth(2)), IG4) == true
@test hybridalphasat(FiniteIndexTruth(1), →(parseformula("p"), FiniteIndexTruth(3)), IG4) == true
@test hybridalphasat(FiniteIndexTruth(1), →(parseformula("p"), FiniteIndexTruth(4)), IG4) == true
@test hybridalphasat(FiniteIndexTruth(1), →(parseformula("p"), FiniteIndexTruth(1)), IG4) == true

@test hybridalphasat(FiniteIndexTruth(2), →(FiniteIndexTruth(2), parseformula("p")), IG4) == true
@test hybridalphasat(FiniteIndexTruth(2), →(FiniteIndexTruth(3), parseformula("p")), IG4) == true
@test hybridalphasat(FiniteIndexTruth(2), →(FiniteIndexTruth(4), parseformula("p")), IG4) == true
@test hybridalphasat(FiniteIndexTruth(2), →(FiniteIndexTruth(1), parseformula("p")), IG4) == true
@test hybridalphasat(FiniteIndexTruth(3), →(FiniteIndexTruth(2), parseformula("p")), IG4) == true
@test hybridalphasat(FiniteIndexTruth(3), →(FiniteIndexTruth(3), parseformula("p")), IG4) == true
@test hybridalphasat(FiniteIndexTruth(3), →(FiniteIndexTruth(4), parseformula("p")), IG4) == true
@test hybridalphasat(FiniteIndexTruth(3), →(FiniteIndexTruth(1), parseformula("p")), IG4) == true
@test hybridalphasat(FiniteIndexTruth(4), →(FiniteIndexTruth(2), parseformula("p")), IG4) == true
@test hybridalphasat(FiniteIndexTruth(4), →(FiniteIndexTruth(3), parseformula("p")), IG4) == true
@test hybridalphasat(FiniteIndexTruth(4), →(FiniteIndexTruth(4), parseformula("p")), IG4) == true
@test hybridalphasat(FiniteIndexTruth(4), →(FiniteIndexTruth(1), parseformula("p")), IG4) == true
@test hybridalphasat(FiniteIndexTruth(1), →(FiniteIndexTruth(2), parseformula("p")), IG4) == true
@test hybridalphasat(FiniteIndexTruth(1), →(FiniteIndexTruth(3), parseformula("p")), IG4) == true
@test hybridalphasat(FiniteIndexTruth(1), →(FiniteIndexTruth(4), parseformula("p")), IG4) == true
@test hybridalphasat(FiniteIndexTruth(1), →(FiniteIndexTruth(1), parseformula("p")), IG4) == true

@test hybridalphasat(FiniteIndexTruth(2), →(parseformula("p"), parseformula("p")), IG4) == true
@test hybridalphasat(FiniteIndexTruth(3), →(parseformula("p"), parseformula("p")), IG4) == true
@test hybridalphasat(FiniteIndexTruth(4), →(parseformula("p"), parseformula("p")), IG4) == true
@test hybridalphasat(FiniteIndexTruth(1), →(parseformula("p"), parseformula("p")), IG4) == true

@test hybridalphasat(FiniteIndexTruth(2), →(parseformula("p"), parseformula("q")), IG4) == true
@test hybridalphasat(FiniteIndexTruth(3), →(parseformula("p"), parseformula("q")), IG4) == true
@test hybridalphasat(FiniteIndexTruth(4), →(parseformula("p"), parseformula("q")), IG4) == true
@test hybridalphasat(FiniteIndexTruth(1), →(parseformula("p"), parseformula("q")), IG4) == true

@test hybridalphasat(FiniteIndexTruth(2), →(parseformula("q"), parseformula("p")), IG4) == true
@test hybridalphasat(FiniteIndexTruth(3), →(parseformula("q"), parseformula("p")), IG4) == true
@test hybridalphasat(FiniteIndexTruth(4), →(parseformula("q"), parseformula("p")), IG4) == true
@test hybridalphasat(FiniteIndexTruth(1), →(parseformula("q"), parseformula("p")), IG4) == true

###########################################################################################
### IH4 ####################################################################################
###########################################################################################

using SoleLogics.ManyValuedLogics: H4

IH4 = convert(FiniteIndexFLewAlgebra, H4)

############################################################################################
## Base cases ##############################################################################
############################################################################################

@test hybridalphasat(FiniteIndexTruth(2), FiniteIndexTruth(2), IH4) == true
@test hybridalphasat(FiniteIndexTruth(2), FiniteIndexTruth(3), IH4) == true
@test hybridalphasat(FiniteIndexTruth(2), FiniteIndexTruth(4), IH4) == true
@test hybridalphasat(FiniteIndexTruth(2), FiniteIndexTruth(1), IH4) == true
@test hybridalphasat(FiniteIndexTruth(3), FiniteIndexTruth(2), IH4) == false
@test hybridalphasat(FiniteIndexTruth(3), FiniteIndexTruth(3), IH4) == true
@test hybridalphasat(FiniteIndexTruth(3), FiniteIndexTruth(4), IH4) == false
@test hybridalphasat(FiniteIndexTruth(3), FiniteIndexTruth(1), IH4) == true
@test hybridalphasat(FiniteIndexTruth(4), FiniteIndexTruth(2), IH4) == false
@test hybridalphasat(FiniteIndexTruth(4), FiniteIndexTruth(3), IH4) == false
@test hybridalphasat(FiniteIndexTruth(4), FiniteIndexTruth(4), IH4) == true
@test hybridalphasat(FiniteIndexTruth(4), FiniteIndexTruth(1), IH4) == true
@test hybridalphasat(FiniteIndexTruth(1), FiniteIndexTruth(2), IH4) == false
@test hybridalphasat(FiniteIndexTruth(1), FiniteIndexTruth(3), IH4) == false
@test hybridalphasat(FiniteIndexTruth(1), FiniteIndexTruth(4), IH4) == false
@test hybridalphasat(FiniteIndexTruth(1), FiniteIndexTruth(1), IH4) == true

@test hybridalphasat(FiniteIndexTruth(2), parseformula("p"), IH4) == true
@test hybridalphasat(FiniteIndexTruth(3), parseformula("p"), IH4) == true
@test hybridalphasat(FiniteIndexTruth(4), parseformula("p"), IH4) == true
@test hybridalphasat(FiniteIndexTruth(1), parseformula("p"), IH4) == true

############################################################################################
## (Strong) disjuction #####################################################################
############################################################################################

@test hybridalphasat(FiniteIndexTruth(2), ∨(FiniteIndexTruth(2), FiniteIndexTruth(2)), IH4) == true
@test hybridalphasat(FiniteIndexTruth(2), ∨(FiniteIndexTruth(2), FiniteIndexTruth(3)), IH4) == true
@test hybridalphasat(FiniteIndexTruth(2), ∨(FiniteIndexTruth(2), FiniteIndexTruth(4)), IH4) == true
@test hybridalphasat(FiniteIndexTruth(2), ∨(FiniteIndexTruth(2), FiniteIndexTruth(1)), IH4) == true
@test hybridalphasat(FiniteIndexTruth(2), ∨(FiniteIndexTruth(3), FiniteIndexTruth(2)), IH4) == true
@test hybridalphasat(FiniteIndexTruth(2), ∨(FiniteIndexTruth(3), FiniteIndexTruth(3)), IH4) == true
@test hybridalphasat(FiniteIndexTruth(2), ∨(FiniteIndexTruth(3), FiniteIndexTruth(4)), IH4) == true
@test hybridalphasat(FiniteIndexTruth(2), ∨(FiniteIndexTruth(3), FiniteIndexTruth(1)), IH4) == true
@test hybridalphasat(FiniteIndexTruth(2), ∨(FiniteIndexTruth(4), FiniteIndexTruth(2)), IH4) == true
@test hybridalphasat(FiniteIndexTruth(2), ∨(FiniteIndexTruth(4), FiniteIndexTruth(3)), IH4) == true
@test hybridalphasat(FiniteIndexTruth(2), ∨(FiniteIndexTruth(4), FiniteIndexTruth(4)), IH4) == true
@test hybridalphasat(FiniteIndexTruth(2), ∨(FiniteIndexTruth(4), FiniteIndexTruth(1)), IH4) == true
@test hybridalphasat(FiniteIndexTruth(2), ∨(FiniteIndexTruth(1), FiniteIndexTruth(2)), IH4) == true
@test hybridalphasat(FiniteIndexTruth(2), ∨(FiniteIndexTruth(1), FiniteIndexTruth(3)), IH4) == true
@test hybridalphasat(FiniteIndexTruth(2), ∨(FiniteIndexTruth(1), FiniteIndexTruth(4)), IH4) == true
@test hybridalphasat(FiniteIndexTruth(2), ∨(FiniteIndexTruth(1), FiniteIndexTruth(1)), IH4) == true

@test hybridalphasat(FiniteIndexTruth(3), ∨(FiniteIndexTruth(2), FiniteIndexTruth(2)), IH4) == false
@test hybridalphasat(FiniteIndexTruth(3), ∨(FiniteIndexTruth(2), FiniteIndexTruth(3)), IH4) == true
@test hybridalphasat(FiniteIndexTruth(3), ∨(FiniteIndexTruth(2), FiniteIndexTruth(4)), IH4) == false
@test hybridalphasat(FiniteIndexTruth(3), ∨(FiniteIndexTruth(2), FiniteIndexTruth(1)), IH4) == true
@test hybridalphasat(FiniteIndexTruth(3), ∨(FiniteIndexTruth(3), FiniteIndexTruth(2)), IH4) == true
@test hybridalphasat(FiniteIndexTruth(3), ∨(FiniteIndexTruth(3), FiniteIndexTruth(3)), IH4) == true
@test hybridalphasat(FiniteIndexTruth(3), ∨(FiniteIndexTruth(3), FiniteIndexTruth(4)), IH4) == true
@test hybridalphasat(FiniteIndexTruth(3), ∨(FiniteIndexTruth(3), FiniteIndexTruth(1)), IH4) == true
@test hybridalphasat(FiniteIndexTruth(3), ∨(FiniteIndexTruth(4), FiniteIndexTruth(2)), IH4) == false
@test hybridalphasat(FiniteIndexTruth(3), ∨(FiniteIndexTruth(4), FiniteIndexTruth(3)), IH4) == true
@test hybridalphasat(FiniteIndexTruth(3), ∨(FiniteIndexTruth(4), FiniteIndexTruth(4)), IH4) == false
@test hybridalphasat(FiniteIndexTruth(3), ∨(FiniteIndexTruth(4), FiniteIndexTruth(1)), IH4) == true
@test hybridalphasat(FiniteIndexTruth(3), ∨(FiniteIndexTruth(1), FiniteIndexTruth(2)), IH4) == true
@test hybridalphasat(FiniteIndexTruth(3), ∨(FiniteIndexTruth(1), FiniteIndexTruth(3)), IH4) == true
@test hybridalphasat(FiniteIndexTruth(3), ∨(FiniteIndexTruth(1), FiniteIndexTruth(4)), IH4) == true
@test hybridalphasat(FiniteIndexTruth(3), ∨(FiniteIndexTruth(1), FiniteIndexTruth(1)), IH4) == true

@test hybridalphasat(FiniteIndexTruth(4), ∨(FiniteIndexTruth(2), FiniteIndexTruth(2)), IH4) == false
@test hybridalphasat(FiniteIndexTruth(4), ∨(FiniteIndexTruth(2), FiniteIndexTruth(3)), IH4) == false
@test hybridalphasat(FiniteIndexTruth(4), ∨(FiniteIndexTruth(2), FiniteIndexTruth(4)), IH4) == true
@test hybridalphasat(FiniteIndexTruth(4), ∨(FiniteIndexTruth(2), FiniteIndexTruth(1)), IH4) == true
@test hybridalphasat(FiniteIndexTruth(4), ∨(FiniteIndexTruth(3), FiniteIndexTruth(2)), IH4) == false
@test hybridalphasat(FiniteIndexTruth(4), ∨(FiniteIndexTruth(3), FiniteIndexTruth(3)), IH4) == false
@test hybridalphasat(FiniteIndexTruth(4), ∨(FiniteIndexTruth(3), FiniteIndexTruth(4)), IH4) == true
@test hybridalphasat(FiniteIndexTruth(4), ∨(FiniteIndexTruth(3), FiniteIndexTruth(1)), IH4) == true
@test hybridalphasat(FiniteIndexTruth(4), ∨(FiniteIndexTruth(4), FiniteIndexTruth(2)), IH4) == true
@test hybridalphasat(FiniteIndexTruth(4), ∨(FiniteIndexTruth(4), FiniteIndexTruth(3)), IH4) == true
@test hybridalphasat(FiniteIndexTruth(4), ∨(FiniteIndexTruth(4), FiniteIndexTruth(4)), IH4) == true
@test hybridalphasat(FiniteIndexTruth(4), ∨(FiniteIndexTruth(4), FiniteIndexTruth(1)), IH4) == true
@test hybridalphasat(FiniteIndexTruth(4), ∨(FiniteIndexTruth(1), FiniteIndexTruth(2)), IH4) == true
@test hybridalphasat(FiniteIndexTruth(4), ∨(FiniteIndexTruth(1), FiniteIndexTruth(3)), IH4) == true
@test hybridalphasat(FiniteIndexTruth(4), ∨(FiniteIndexTruth(1), FiniteIndexTruth(4)), IH4) == true
@test hybridalphasat(FiniteIndexTruth(4), ∨(FiniteIndexTruth(1), FiniteIndexTruth(1)), IH4) == true

@test hybridalphasat(FiniteIndexTruth(1), ∨(FiniteIndexTruth(2), FiniteIndexTruth(2)), IH4) == false
@test hybridalphasat(FiniteIndexTruth(1), ∨(FiniteIndexTruth(2), FiniteIndexTruth(3)), IH4) == false
@test hybridalphasat(FiniteIndexTruth(1), ∨(FiniteIndexTruth(2), FiniteIndexTruth(4)), IH4) == false
@test hybridalphasat(FiniteIndexTruth(1), ∨(FiniteIndexTruth(2), FiniteIndexTruth(1)), IH4) == true
@test hybridalphasat(FiniteIndexTruth(1), ∨(FiniteIndexTruth(3), FiniteIndexTruth(2)), IH4) == false
@test hybridalphasat(FiniteIndexTruth(1), ∨(FiniteIndexTruth(3), FiniteIndexTruth(3)), IH4) == false
@test hybridalphasat(FiniteIndexTruth(1), ∨(FiniteIndexTruth(3), FiniteIndexTruth(4)), IH4) == true
@test hybridalphasat(FiniteIndexTruth(1), ∨(FiniteIndexTruth(3), FiniteIndexTruth(1)), IH4) == true
@test hybridalphasat(FiniteIndexTruth(1), ∨(FiniteIndexTruth(4), FiniteIndexTruth(2)), IH4) == false
@test hybridalphasat(FiniteIndexTruth(1), ∨(FiniteIndexTruth(4), FiniteIndexTruth(3)), IH4) == true
@test hybridalphasat(FiniteIndexTruth(1), ∨(FiniteIndexTruth(4), FiniteIndexTruth(4)), IH4) == false
@test hybridalphasat(FiniteIndexTruth(1), ∨(FiniteIndexTruth(4), FiniteIndexTruth(1)), IH4) == true
@test hybridalphasat(FiniteIndexTruth(1), ∨(FiniteIndexTruth(1), FiniteIndexTruth(2)), IH4) == true
@test hybridalphasat(FiniteIndexTruth(1), ∨(FiniteIndexTruth(1), FiniteIndexTruth(3)), IH4) == true
@test hybridalphasat(FiniteIndexTruth(1), ∨(FiniteIndexTruth(1), FiniteIndexTruth(4)), IH4) == true
@test hybridalphasat(FiniteIndexTruth(1), ∨(FiniteIndexTruth(1), FiniteIndexTruth(1)), IH4) == true

@test hybridalphasat(FiniteIndexTruth(2), ∨(parseformula("p"), FiniteIndexTruth(2)), IH4) == true
@test hybridalphasat(FiniteIndexTruth(2), ∨(parseformula("p"), FiniteIndexTruth(3)), IH4) == true
@test hybridalphasat(FiniteIndexTruth(2), ∨(parseformula("p"), FiniteIndexTruth(4)), IH4) == true
@test hybridalphasat(FiniteIndexTruth(2), ∨(parseformula("p"), FiniteIndexTruth(1)), IH4) == true
@test hybridalphasat(FiniteIndexTruth(3), ∨(parseformula("p"), FiniteIndexTruth(2)), IH4) == true
@test hybridalphasat(FiniteIndexTruth(3), ∨(parseformula("p"), FiniteIndexTruth(3)), IH4) == true
@test hybridalphasat(FiniteIndexTruth(3), ∨(parseformula("p"), FiniteIndexTruth(4)), IH4) == true
@test hybridalphasat(FiniteIndexTruth(3), ∨(parseformula("p"), FiniteIndexTruth(1)), IH4) == true
@test hybridalphasat(FiniteIndexTruth(4), ∨(parseformula("p"), FiniteIndexTruth(2)), IH4) == true
@test hybridalphasat(FiniteIndexTruth(4), ∨(parseformula("p"), FiniteIndexTruth(3)), IH4) == true
@test hybridalphasat(FiniteIndexTruth(4), ∨(parseformula("p"), FiniteIndexTruth(4)), IH4) == true
@test hybridalphasat(FiniteIndexTruth(4), ∨(parseformula("p"), FiniteIndexTruth(1)), IH4) == true
@test hybridalphasat(FiniteIndexTruth(1), ∨(parseformula("p"), FiniteIndexTruth(2)), IH4) == true
@test hybridalphasat(FiniteIndexTruth(1), ∨(parseformula("p"), FiniteIndexTruth(3)), IH4) == true
@test hybridalphasat(FiniteIndexTruth(1), ∨(parseformula("p"), FiniteIndexTruth(4)), IH4) == true
@test hybridalphasat(FiniteIndexTruth(1), ∨(parseformula("p"), FiniteIndexTruth(1)), IH4) == true

@test hybridalphasat(FiniteIndexTruth(2), ∨(FiniteIndexTruth(2), parseformula("p")), IH4) == true
@test hybridalphasat(FiniteIndexTruth(2), ∨(FiniteIndexTruth(3), parseformula("p")), IH4) == true
@test hybridalphasat(FiniteIndexTruth(2), ∨(FiniteIndexTruth(4), parseformula("p")), IH4) == true
@test hybridalphasat(FiniteIndexTruth(2), ∨(FiniteIndexTruth(1), parseformula("p")), IH4) == true
@test hybridalphasat(FiniteIndexTruth(3), ∨(FiniteIndexTruth(2), parseformula("p")), IH4) == true
@test hybridalphasat(FiniteIndexTruth(3), ∨(FiniteIndexTruth(3), parseformula("p")), IH4) == true
@test hybridalphasat(FiniteIndexTruth(3), ∨(FiniteIndexTruth(4), parseformula("p")), IH4) == true
@test hybridalphasat(FiniteIndexTruth(3), ∨(FiniteIndexTruth(1), parseformula("p")), IH4) == true
@test hybridalphasat(FiniteIndexTruth(4), ∨(FiniteIndexTruth(2), parseformula("p")), IH4) == true
@test hybridalphasat(FiniteIndexTruth(4), ∨(FiniteIndexTruth(3), parseformula("p")), IH4) == true
@test hybridalphasat(FiniteIndexTruth(4), ∨(FiniteIndexTruth(4), parseformula("p")), IH4) == true
@test hybridalphasat(FiniteIndexTruth(4), ∨(FiniteIndexTruth(1), parseformula("p")), IH4) == true
@test hybridalphasat(FiniteIndexTruth(1), ∨(FiniteIndexTruth(2), parseformula("p")), IH4) == true
@test hybridalphasat(FiniteIndexTruth(1), ∨(FiniteIndexTruth(3), parseformula("p")), IH4) == true
@test hybridalphasat(FiniteIndexTruth(1), ∨(FiniteIndexTruth(4), parseformula("p")), IH4) == true
@test hybridalphasat(FiniteIndexTruth(1), ∨(FiniteIndexTruth(1), parseformula("p")), IH4) == true

@test hybridalphasat(FiniteIndexTruth(2), ∨(parseformula("p"), parseformula("p")), IH4) == true
@test hybridalphasat(FiniteIndexTruth(3), ∨(parseformula("p"), parseformula("p")), IH4) == true
@test hybridalphasat(FiniteIndexTruth(4), ∨(parseformula("p"), parseformula("p")), IH4) == true
@test hybridalphasat(FiniteIndexTruth(1), ∨(parseformula("p"), parseformula("p")), IH4) == true

@test hybridalphasat(FiniteIndexTruth(2), ∨(parseformula("p"), parseformula("q")), IH4) == true
@test hybridalphasat(FiniteIndexTruth(3), ∨(parseformula("p"), parseformula("q")), IH4) == true
@test hybridalphasat(FiniteIndexTruth(4), ∨(parseformula("p"), parseformula("q")), IH4) == true
@test hybridalphasat(FiniteIndexTruth(1), ∨(parseformula("p"), parseformula("q")), IH4) == true

@test hybridalphasat(FiniteIndexTruth(2), ∨(parseformula("q"), parseformula("q")), IH4) == true
@test hybridalphasat(FiniteIndexTruth(3), ∨(parseformula("q"), parseformula("q")), IH4) == true
@test hybridalphasat(FiniteIndexTruth(4), ∨(parseformula("q"), parseformula("q")), IH4) == true
@test hybridalphasat(FiniteIndexTruth(1), ∨(parseformula("q"), parseformula("q")), IH4) == true

############################################################################################
## (Strong) conjunction ####################################################################
############################################################################################

@test hybridalphasat(FiniteIndexTruth(2), ∧(FiniteIndexTruth(2), FiniteIndexTruth(2)), IH4) == true
@test hybridalphasat(FiniteIndexTruth(2), ∧(FiniteIndexTruth(2), FiniteIndexTruth(3)), IH4) == true
@test hybridalphasat(FiniteIndexTruth(2), ∧(FiniteIndexTruth(2), FiniteIndexTruth(4)), IH4) == true
@test hybridalphasat(FiniteIndexTruth(2), ∧(FiniteIndexTruth(2), FiniteIndexTruth(1)), IH4) == true
@test hybridalphasat(FiniteIndexTruth(2), ∧(FiniteIndexTruth(3), FiniteIndexTruth(2)), IH4) == true
@test hybridalphasat(FiniteIndexTruth(2), ∧(FiniteIndexTruth(3), FiniteIndexTruth(3)), IH4) == true
@test hybridalphasat(FiniteIndexTruth(2), ∧(FiniteIndexTruth(3), FiniteIndexTruth(4)), IH4) == true
@test hybridalphasat(FiniteIndexTruth(2), ∧(FiniteIndexTruth(3), FiniteIndexTruth(1)), IH4) == true
@test hybridalphasat(FiniteIndexTruth(2), ∧(FiniteIndexTruth(4), FiniteIndexTruth(2)), IH4) == true
@test hybridalphasat(FiniteIndexTruth(2), ∧(FiniteIndexTruth(4), FiniteIndexTruth(3)), IH4) == true
@test hybridalphasat(FiniteIndexTruth(2), ∧(FiniteIndexTruth(4), FiniteIndexTruth(4)), IH4) == true
@test hybridalphasat(FiniteIndexTruth(2), ∧(FiniteIndexTruth(4), FiniteIndexTruth(1)), IH4) == true
@test hybridalphasat(FiniteIndexTruth(2), ∧(FiniteIndexTruth(1), FiniteIndexTruth(2)), IH4) == true
@test hybridalphasat(FiniteIndexTruth(2), ∧(FiniteIndexTruth(1), FiniteIndexTruth(3)), IH4) == true
@test hybridalphasat(FiniteIndexTruth(2), ∧(FiniteIndexTruth(1), FiniteIndexTruth(4)), IH4) == true
@test hybridalphasat(FiniteIndexTruth(2), ∧(FiniteIndexTruth(1), FiniteIndexTruth(1)), IH4) == true

@test hybridalphasat(FiniteIndexTruth(3), ∧(FiniteIndexTruth(2), FiniteIndexTruth(2)), IH4) == false
@test hybridalphasat(FiniteIndexTruth(3), ∧(FiniteIndexTruth(2), FiniteIndexTruth(3)), IH4) == false
@test hybridalphasat(FiniteIndexTruth(3), ∧(FiniteIndexTruth(2), FiniteIndexTruth(4)), IH4) == false
@test hybridalphasat(FiniteIndexTruth(3), ∧(FiniteIndexTruth(2), FiniteIndexTruth(1)), IH4) == false
@test hybridalphasat(FiniteIndexTruth(3), ∧(FiniteIndexTruth(3), FiniteIndexTruth(2)), IH4) == false
@test hybridalphasat(FiniteIndexTruth(3), ∧(FiniteIndexTruth(3), FiniteIndexTruth(3)), IH4) == true
@test hybridalphasat(FiniteIndexTruth(3), ∧(FiniteIndexTruth(3), FiniteIndexTruth(4)), IH4) == false
@test hybridalphasat(FiniteIndexTruth(3), ∧(FiniteIndexTruth(3), FiniteIndexTruth(1)), IH4) == true
@test hybridalphasat(FiniteIndexTruth(3), ∧(FiniteIndexTruth(4), FiniteIndexTruth(2)), IH4) == false
@test hybridalphasat(FiniteIndexTruth(3), ∧(FiniteIndexTruth(4), FiniteIndexTruth(3)), IH4) == false
@test hybridalphasat(FiniteIndexTruth(3), ∧(FiniteIndexTruth(4), FiniteIndexTruth(4)), IH4) == false
@test hybridalphasat(FiniteIndexTruth(3), ∧(FiniteIndexTruth(4), FiniteIndexTruth(1)), IH4) == false
@test hybridalphasat(FiniteIndexTruth(3), ∧(FiniteIndexTruth(1), FiniteIndexTruth(2)), IH4) == false
@test hybridalphasat(FiniteIndexTruth(3), ∧(FiniteIndexTruth(1), FiniteIndexTruth(3)), IH4) == true
@test hybridalphasat(FiniteIndexTruth(3), ∧(FiniteIndexTruth(1), FiniteIndexTruth(4)), IH4) == false
@test hybridalphasat(FiniteIndexTruth(3), ∧(FiniteIndexTruth(1), FiniteIndexTruth(1)), IH4) == true

@test hybridalphasat(FiniteIndexTruth(4), ∧(FiniteIndexTruth(2), FiniteIndexTruth(2)), IH4) == false
@test hybridalphasat(FiniteIndexTruth(4), ∧(FiniteIndexTruth(2), FiniteIndexTruth(3)), IH4) == false
@test hybridalphasat(FiniteIndexTruth(4), ∧(FiniteIndexTruth(2), FiniteIndexTruth(4)), IH4) == false
@test hybridalphasat(FiniteIndexTruth(4), ∧(FiniteIndexTruth(2), FiniteIndexTruth(1)), IH4) == false
@test hybridalphasat(FiniteIndexTruth(4), ∧(FiniteIndexTruth(3), FiniteIndexTruth(2)), IH4) == false
@test hybridalphasat(FiniteIndexTruth(4), ∧(FiniteIndexTruth(3), FiniteIndexTruth(3)), IH4) == false
@test hybridalphasat(FiniteIndexTruth(4), ∧(FiniteIndexTruth(3), FiniteIndexTruth(4)), IH4) == false
@test hybridalphasat(FiniteIndexTruth(4), ∧(FiniteIndexTruth(3), FiniteIndexTruth(1)), IH4) == false
@test hybridalphasat(FiniteIndexTruth(4), ∧(FiniteIndexTruth(4), FiniteIndexTruth(2)), IH4) == false
@test hybridalphasat(FiniteIndexTruth(4), ∧(FiniteIndexTruth(4), FiniteIndexTruth(3)), IH4) == false
@test hybridalphasat(FiniteIndexTruth(4), ∧(FiniteIndexTruth(4), FiniteIndexTruth(4)), IH4) == true
@test hybridalphasat(FiniteIndexTruth(4), ∧(FiniteIndexTruth(4), FiniteIndexTruth(1)), IH4) == true
@test hybridalphasat(FiniteIndexTruth(4), ∧(FiniteIndexTruth(1), FiniteIndexTruth(2)), IH4) == false
@test hybridalphasat(FiniteIndexTruth(4), ∧(FiniteIndexTruth(1), FiniteIndexTruth(3)), IH4) == false
@test hybridalphasat(FiniteIndexTruth(4), ∧(FiniteIndexTruth(1), FiniteIndexTruth(4)), IH4) == true
@test hybridalphasat(FiniteIndexTruth(4), ∧(FiniteIndexTruth(1), FiniteIndexTruth(1)), IH4) == true

@test hybridalphasat(FiniteIndexTruth(1), ∧(FiniteIndexTruth(2), FiniteIndexTruth(2)), IH4) == false
@test hybridalphasat(FiniteIndexTruth(1), ∧(FiniteIndexTruth(2), FiniteIndexTruth(3)), IH4) == false
@test hybridalphasat(FiniteIndexTruth(1), ∧(FiniteIndexTruth(2), FiniteIndexTruth(4)), IH4) == false
@test hybridalphasat(FiniteIndexTruth(1), ∧(FiniteIndexTruth(2), FiniteIndexTruth(1)), IH4) == false
@test hybridalphasat(FiniteIndexTruth(1), ∧(FiniteIndexTruth(3), FiniteIndexTruth(2)), IH4) == false
@test hybridalphasat(FiniteIndexTruth(1), ∧(FiniteIndexTruth(3), FiniteIndexTruth(3)), IH4) == false
@test hybridalphasat(FiniteIndexTruth(1), ∧(FiniteIndexTruth(3), FiniteIndexTruth(4)), IH4) == false
@test hybridalphasat(FiniteIndexTruth(1), ∧(FiniteIndexTruth(3), FiniteIndexTruth(1)), IH4) == false
@test hybridalphasat(FiniteIndexTruth(1), ∧(FiniteIndexTruth(4), FiniteIndexTruth(2)), IH4) == false
@test hybridalphasat(FiniteIndexTruth(1), ∧(FiniteIndexTruth(4), FiniteIndexTruth(3)), IH4) == false
@test hybridalphasat(FiniteIndexTruth(1), ∧(FiniteIndexTruth(4), FiniteIndexTruth(4)), IH4) == false
@test hybridalphasat(FiniteIndexTruth(1), ∧(FiniteIndexTruth(4), FiniteIndexTruth(1)), IH4) == false
@test hybridalphasat(FiniteIndexTruth(1), ∧(FiniteIndexTruth(1), FiniteIndexTruth(2)), IH4) == false
@test hybridalphasat(FiniteIndexTruth(1), ∧(FiniteIndexTruth(1), FiniteIndexTruth(3)), IH4) == false
@test hybridalphasat(FiniteIndexTruth(1), ∧(FiniteIndexTruth(1), FiniteIndexTruth(4)), IH4) == false
@test hybridalphasat(FiniteIndexTruth(1), ∧(FiniteIndexTruth(1), FiniteIndexTruth(1)), IH4) == true

@test hybridalphasat(FiniteIndexTruth(2), ∧(parseformula("p"), FiniteIndexTruth(2)), IH4) == true
@test hybridalphasat(FiniteIndexTruth(2), ∧(parseformula("p"), FiniteIndexTruth(3)), IH4) == true
@test hybridalphasat(FiniteIndexTruth(2), ∧(parseformula("p"), FiniteIndexTruth(4)), IH4) == true
@test hybridalphasat(FiniteIndexTruth(2), ∧(parseformula("p"), FiniteIndexTruth(1)), IH4) == true
@test hybridalphasat(FiniteIndexTruth(3), ∧(parseformula("p"), FiniteIndexTruth(2)), IH4) == false
@test hybridalphasat(FiniteIndexTruth(3), ∧(parseformula("p"), FiniteIndexTruth(3)), IH4) == true
@test hybridalphasat(FiniteIndexTruth(3), ∧(parseformula("p"), FiniteIndexTruth(4)), IH4) == false
@test hybridalphasat(FiniteIndexTruth(3), ∧(parseformula("p"), FiniteIndexTruth(1)), IH4) == true
@test hybridalphasat(FiniteIndexTruth(4), ∧(parseformula("p"), FiniteIndexTruth(2)), IH4) == false
@test hybridalphasat(FiniteIndexTruth(4), ∧(parseformula("p"), FiniteIndexTruth(3)), IH4) == false
@test hybridalphasat(FiniteIndexTruth(4), ∧(parseformula("p"), FiniteIndexTruth(4)), IH4) == true
@test hybridalphasat(FiniteIndexTruth(4), ∧(parseformula("p"), FiniteIndexTruth(1)), IH4) == true
@test hybridalphasat(FiniteIndexTruth(1), ∧(parseformula("p"), FiniteIndexTruth(2)), IH4) == false
@test hybridalphasat(FiniteIndexTruth(1), ∧(parseformula("p"), FiniteIndexTruth(3)), IH4) == false
@test hybridalphasat(FiniteIndexTruth(1), ∧(parseformula("p"), FiniteIndexTruth(4)), IH4) == false
@test hybridalphasat(FiniteIndexTruth(1), ∧(parseformula("p"), FiniteIndexTruth(1)), IH4) == true

@test hybridalphasat(FiniteIndexTruth(2), ∧(FiniteIndexTruth(2), parseformula("p")), IH4) == true
@test hybridalphasat(FiniteIndexTruth(2), ∧(FiniteIndexTruth(3), parseformula("p")), IH4) == true
@test hybridalphasat(FiniteIndexTruth(2), ∧(FiniteIndexTruth(4), parseformula("p")), IH4) == true
@test hybridalphasat(FiniteIndexTruth(2), ∧(FiniteIndexTruth(1), parseformula("p")), IH4) == true
@test hybridalphasat(FiniteIndexTruth(3), ∧(FiniteIndexTruth(2), parseformula("p")), IH4) == false
@test hybridalphasat(FiniteIndexTruth(3), ∧(FiniteIndexTruth(3), parseformula("p")), IH4) == true
@test hybridalphasat(FiniteIndexTruth(3), ∧(FiniteIndexTruth(4), parseformula("p")), IH4) == false
@test hybridalphasat(FiniteIndexTruth(3), ∧(FiniteIndexTruth(1), parseformula("p")), IH4) == true
@test hybridalphasat(FiniteIndexTruth(4), ∧(FiniteIndexTruth(2), parseformula("p")), IH4) == false
@test hybridalphasat(FiniteIndexTruth(4), ∧(FiniteIndexTruth(3), parseformula("p")), IH4) == false
@test hybridalphasat(FiniteIndexTruth(4), ∧(FiniteIndexTruth(4), parseformula("p")), IH4) == true
@test hybridalphasat(FiniteIndexTruth(4), ∧(FiniteIndexTruth(1), parseformula("p")), IH4) == true
@test hybridalphasat(FiniteIndexTruth(1), ∧(FiniteIndexTruth(2), parseformula("p")), IH4) == false
@test hybridalphasat(FiniteIndexTruth(1), ∧(FiniteIndexTruth(3), parseformula("p")), IH4) == false
@test hybridalphasat(FiniteIndexTruth(1), ∧(FiniteIndexTruth(4), parseformula("p")), IH4) == false
@test hybridalphasat(FiniteIndexTruth(1), ∧(FiniteIndexTruth(1), parseformula("p")), IH4) == true

@test hybridalphasat(FiniteIndexTruth(2), ∧(parseformula("p"), parseformula("p")), IH4) == true
@test hybridalphasat(FiniteIndexTruth(3), ∧(parseformula("p"), parseformula("p")), IH4) == true
@test hybridalphasat(FiniteIndexTruth(4), ∧(parseformula("p"), parseformula("p")), IH4) == true
@test hybridalphasat(FiniteIndexTruth(1), ∧(parseformula("p"), parseformula("p")), IH4) == true

@test hybridalphasat(FiniteIndexTruth(2), ∧(parseformula("p"), parseformula("q")), IH4) == true
@test hybridalphasat(FiniteIndexTruth(3), ∧(parseformula("p"), parseformula("q")), IH4) == true
@test hybridalphasat(FiniteIndexTruth(4), ∧(parseformula("p"), parseformula("q")), IH4) == true
@test hybridalphasat(FiniteIndexTruth(1), ∧(parseformula("p"), parseformula("q")), IH4) == true

@test hybridalphasat(FiniteIndexTruth(2), ∧(parseformula("q"), parseformula("p")), IH4) == true
@test hybridalphasat(FiniteIndexTruth(3), ∧(parseformula("q"), parseformula("p")), IH4) == true
@test hybridalphasat(FiniteIndexTruth(4), ∧(parseformula("q"), parseformula("p")), IH4) == true
@test hybridalphasat(FiniteIndexTruth(1), ∧(parseformula("q"), parseformula("p")), IH4) == true

############################################################################################
## Implication #############################################################################
############################################################################################

@test hybridalphasat(FiniteIndexTruth(2), →(FiniteIndexTruth(2), FiniteIndexTruth(2)), IH4) == true
@test hybridalphasat(FiniteIndexTruth(2), →(FiniteIndexTruth(2), FiniteIndexTruth(3)), IH4) == true
@test hybridalphasat(FiniteIndexTruth(2), →(FiniteIndexTruth(2), FiniteIndexTruth(4)), IH4) == true
@test hybridalphasat(FiniteIndexTruth(2), →(FiniteIndexTruth(2), FiniteIndexTruth(1)), IH4) == true
@test hybridalphasat(FiniteIndexTruth(2), →(FiniteIndexTruth(3), FiniteIndexTruth(2)), IH4) == true
@test hybridalphasat(FiniteIndexTruth(2), →(FiniteIndexTruth(3), FiniteIndexTruth(3)), IH4) == true
@test hybridalphasat(FiniteIndexTruth(2), →(FiniteIndexTruth(3), FiniteIndexTruth(4)), IH4) == true
@test hybridalphasat(FiniteIndexTruth(2), →(FiniteIndexTruth(3), FiniteIndexTruth(1)), IH4) == true
@test hybridalphasat(FiniteIndexTruth(2), →(FiniteIndexTruth(4), FiniteIndexTruth(2)), IH4) == true
@test hybridalphasat(FiniteIndexTruth(2), →(FiniteIndexTruth(4), FiniteIndexTruth(3)), IH4) == true
@test hybridalphasat(FiniteIndexTruth(2), →(FiniteIndexTruth(4), FiniteIndexTruth(4)), IH4) == true
@test hybridalphasat(FiniteIndexTruth(2), →(FiniteIndexTruth(4), FiniteIndexTruth(1)), IH4) == true
@test hybridalphasat(FiniteIndexTruth(2), →(FiniteIndexTruth(1), FiniteIndexTruth(2)), IH4) == true
@test hybridalphasat(FiniteIndexTruth(2), →(FiniteIndexTruth(1), FiniteIndexTruth(3)), IH4) == true
@test hybridalphasat(FiniteIndexTruth(2), →(FiniteIndexTruth(1), FiniteIndexTruth(4)), IH4) == true
@test hybridalphasat(FiniteIndexTruth(2), →(FiniteIndexTruth(1), FiniteIndexTruth(1)), IH4) == true

@test hybridalphasat(FiniteIndexTruth(3), →(FiniteIndexTruth(2), FiniteIndexTruth(2)), IH4) == true
@test hybridalphasat(FiniteIndexTruth(3), →(FiniteIndexTruth(2), FiniteIndexTruth(3)), IH4) == true
@test hybridalphasat(FiniteIndexTruth(3), →(FiniteIndexTruth(2), FiniteIndexTruth(4)), IH4) == true
@test hybridalphasat(FiniteIndexTruth(3), →(FiniteIndexTruth(2), FiniteIndexTruth(1)), IH4) == true
@test hybridalphasat(FiniteIndexTruth(3), →(FiniteIndexTruth(3), FiniteIndexTruth(2)), IH4) == false
@test hybridalphasat(FiniteIndexTruth(3), →(FiniteIndexTruth(3), FiniteIndexTruth(3)), IH4) == true
@test hybridalphasat(FiniteIndexTruth(3), →(FiniteIndexTruth(3), FiniteIndexTruth(4)), IH4) == false
@test hybridalphasat(FiniteIndexTruth(3), →(FiniteIndexTruth(3), FiniteIndexTruth(1)), IH4) == true
@test hybridalphasat(FiniteIndexTruth(3), →(FiniteIndexTruth(4), FiniteIndexTruth(2)), IH4) == true
@test hybridalphasat(FiniteIndexTruth(3), →(FiniteIndexTruth(4), FiniteIndexTruth(3)), IH4) == true
@test hybridalphasat(FiniteIndexTruth(3), →(FiniteIndexTruth(4), FiniteIndexTruth(4)), IH4) == true
@test hybridalphasat(FiniteIndexTruth(3), →(FiniteIndexTruth(4), FiniteIndexTruth(1)), IH4) == true
@test hybridalphasat(FiniteIndexTruth(3), →(FiniteIndexTruth(1), FiniteIndexTruth(2)), IH4) == false
@test hybridalphasat(FiniteIndexTruth(3), →(FiniteIndexTruth(1), FiniteIndexTruth(3)), IH4) == true
@test hybridalphasat(FiniteIndexTruth(3), →(FiniteIndexTruth(1), FiniteIndexTruth(4)), IH4) == false
@test hybridalphasat(FiniteIndexTruth(3), →(FiniteIndexTruth(1), FiniteIndexTruth(1)), IH4) == true

@test hybridalphasat(FiniteIndexTruth(4), →(FiniteIndexTruth(2), FiniteIndexTruth(2)), IH4) == true
@test hybridalphasat(FiniteIndexTruth(4), →(FiniteIndexTruth(2), FiniteIndexTruth(3)), IH4) == true
@test hybridalphasat(FiniteIndexTruth(4), →(FiniteIndexTruth(2), FiniteIndexTruth(4)), IH4) == true
@test hybridalphasat(FiniteIndexTruth(4), →(FiniteIndexTruth(2), FiniteIndexTruth(1)), IH4) == true
@test hybridalphasat(FiniteIndexTruth(4), →(FiniteIndexTruth(3), FiniteIndexTruth(2)), IH4) == true
@test hybridalphasat(FiniteIndexTruth(4), →(FiniteIndexTruth(3), FiniteIndexTruth(3)), IH4) == true
@test hybridalphasat(FiniteIndexTruth(4), →(FiniteIndexTruth(3), FiniteIndexTruth(4)), IH4) == true
@test hybridalphasat(FiniteIndexTruth(4), →(FiniteIndexTruth(3), FiniteIndexTruth(1)), IH4) == true
@test hybridalphasat(FiniteIndexTruth(4), →(FiniteIndexTruth(4), FiniteIndexTruth(2)), IH4) == false
@test hybridalphasat(FiniteIndexTruth(4), →(FiniteIndexTruth(4), FiniteIndexTruth(3)), IH4) == false
@test hybridalphasat(FiniteIndexTruth(4), →(FiniteIndexTruth(4), FiniteIndexTruth(4)), IH4) == true
@test hybridalphasat(FiniteIndexTruth(4), →(FiniteIndexTruth(4), FiniteIndexTruth(1)), IH4) == true
@test hybridalphasat(FiniteIndexTruth(4), →(FiniteIndexTruth(1), FiniteIndexTruth(2)), IH4) == false
@test hybridalphasat(FiniteIndexTruth(4), →(FiniteIndexTruth(1), FiniteIndexTruth(3)), IH4) == false
@test hybridalphasat(FiniteIndexTruth(4), →(FiniteIndexTruth(1), FiniteIndexTruth(4)), IH4) == true
@test hybridalphasat(FiniteIndexTruth(4), →(FiniteIndexTruth(1), FiniteIndexTruth(1)), IH4) == true

@test hybridalphasat(FiniteIndexTruth(1), →(FiniteIndexTruth(2), FiniteIndexTruth(2)), IH4) == true
@test hybridalphasat(FiniteIndexTruth(1), →(FiniteIndexTruth(2), FiniteIndexTruth(3)), IH4) == true
@test hybridalphasat(FiniteIndexTruth(1), →(FiniteIndexTruth(2), FiniteIndexTruth(4)), IH4) == true
@test hybridalphasat(FiniteIndexTruth(1), →(FiniteIndexTruth(2), FiniteIndexTruth(1)), IH4) == true
@test hybridalphasat(FiniteIndexTruth(1), →(FiniteIndexTruth(3), FiniteIndexTruth(2)), IH4) == false
@test hybridalphasat(FiniteIndexTruth(1), →(FiniteIndexTruth(3), FiniteIndexTruth(3)), IH4) == true
@test hybridalphasat(FiniteIndexTruth(1), →(FiniteIndexTruth(3), FiniteIndexTruth(4)), IH4) == false
@test hybridalphasat(FiniteIndexTruth(1), →(FiniteIndexTruth(3), FiniteIndexTruth(1)), IH4) == true
@test hybridalphasat(FiniteIndexTruth(1), →(FiniteIndexTruth(4), FiniteIndexTruth(2)), IH4) == false
@test hybridalphasat(FiniteIndexTruth(1), →(FiniteIndexTruth(4), FiniteIndexTruth(3)), IH4) == false
@test hybridalphasat(FiniteIndexTruth(1), →(FiniteIndexTruth(4), FiniteIndexTruth(4)), IH4) == true
@test hybridalphasat(FiniteIndexTruth(1), →(FiniteIndexTruth(4), FiniteIndexTruth(1)), IH4) == true
@test hybridalphasat(FiniteIndexTruth(1), →(FiniteIndexTruth(1), FiniteIndexTruth(2)), IH4) == false
@test hybridalphasat(FiniteIndexTruth(1), →(FiniteIndexTruth(1), FiniteIndexTruth(3)), IH4) == false
@test hybridalphasat(FiniteIndexTruth(1), →(FiniteIndexTruth(1), FiniteIndexTruth(4)), IH4) == false
@test hybridalphasat(FiniteIndexTruth(1), →(FiniteIndexTruth(1), FiniteIndexTruth(1)), IH4) == true

@test hybridalphasat(FiniteIndexTruth(2), →(parseformula("p"), FiniteIndexTruth(2)), IH4) == true
@test hybridalphasat(FiniteIndexTruth(2), →(parseformula("p"), FiniteIndexTruth(3)), IH4) == true
@test hybridalphasat(FiniteIndexTruth(2), →(parseformula("p"), FiniteIndexTruth(4)), IH4) == true
@test hybridalphasat(FiniteIndexTruth(2), →(parseformula("p"), FiniteIndexTruth(1)), IH4) == true
@test hybridalphasat(FiniteIndexTruth(3), →(parseformula("p"), FiniteIndexTruth(2)), IH4) == true
@test hybridalphasat(FiniteIndexTruth(3), →(parseformula("p"), FiniteIndexTruth(3)), IH4) == true
@test hybridalphasat(FiniteIndexTruth(3), →(parseformula("p"), FiniteIndexTruth(4)), IH4) == true
@test hybridalphasat(FiniteIndexTruth(3), →(parseformula("p"), FiniteIndexTruth(1)), IH4) == true
@test hybridalphasat(FiniteIndexTruth(4), →(parseformula("p"), FiniteIndexTruth(2)), IH4) == true
@test hybridalphasat(FiniteIndexTruth(4), →(parseformula("p"), FiniteIndexTruth(3)), IH4) == true
@test hybridalphasat(FiniteIndexTruth(4), →(parseformula("p"), FiniteIndexTruth(4)), IH4) == true
@test hybridalphasat(FiniteIndexTruth(4), →(parseformula("p"), FiniteIndexTruth(1)), IH4) == true
@test hybridalphasat(FiniteIndexTruth(1), →(parseformula("p"), FiniteIndexTruth(2)), IH4) == true
@test hybridalphasat(FiniteIndexTruth(1), →(parseformula("p"), FiniteIndexTruth(3)), IH4) == true
@test hybridalphasat(FiniteIndexTruth(1), →(parseformula("p"), FiniteIndexTruth(4)), IH4) == true
@test hybridalphasat(FiniteIndexTruth(1), →(parseformula("p"), FiniteIndexTruth(1)), IH4) == true

@test hybridalphasat(FiniteIndexTruth(2), →(FiniteIndexTruth(2), parseformula("p")), IH4) == true
@test hybridalphasat(FiniteIndexTruth(2), →(FiniteIndexTruth(3), parseformula("p")), IH4) == true
@test hybridalphasat(FiniteIndexTruth(2), →(FiniteIndexTruth(4), parseformula("p")), IH4) == true
@test hybridalphasat(FiniteIndexTruth(2), →(FiniteIndexTruth(1), parseformula("p")), IH4) == true
@test hybridalphasat(FiniteIndexTruth(3), →(FiniteIndexTruth(2), parseformula("p")), IH4) == true
@test hybridalphasat(FiniteIndexTruth(3), →(FiniteIndexTruth(3), parseformula("p")), IH4) == true
@test hybridalphasat(FiniteIndexTruth(3), →(FiniteIndexTruth(4), parseformula("p")), IH4) == true
@test hybridalphasat(FiniteIndexTruth(3), →(FiniteIndexTruth(1), parseformula("p")), IH4) == true
@test hybridalphasat(FiniteIndexTruth(4), →(FiniteIndexTruth(2), parseformula("p")), IH4) == true
@test hybridalphasat(FiniteIndexTruth(4), →(FiniteIndexTruth(3), parseformula("p")), IH4) == true
@test hybridalphasat(FiniteIndexTruth(4), →(FiniteIndexTruth(4), parseformula("p")), IH4) == true
@test hybridalphasat(FiniteIndexTruth(4), →(FiniteIndexTruth(1), parseformula("p")), IH4) == true
@test hybridalphasat(FiniteIndexTruth(1), →(FiniteIndexTruth(2), parseformula("p")), IH4) == true
@test hybridalphasat(FiniteIndexTruth(1), →(FiniteIndexTruth(3), parseformula("p")), IH4) == true
@test hybridalphasat(FiniteIndexTruth(1), →(FiniteIndexTruth(4), parseformula("p")), IH4) == true
@test hybridalphasat(FiniteIndexTruth(1), →(FiniteIndexTruth(1), parseformula("p")), IH4) == true

@test hybridalphasat(FiniteIndexTruth(2), →(parseformula("p"), parseformula("p")), IH4) == true
@test hybridalphasat(FiniteIndexTruth(3), →(parseformula("p"), parseformula("p")), IH4) == true
@test hybridalphasat(FiniteIndexTruth(4), →(parseformula("p"), parseformula("p")), IH4) == true
@test hybridalphasat(FiniteIndexTruth(1), →(parseformula("p"), parseformula("p")), IH4) == true

@test hybridalphasat(FiniteIndexTruth(2), →(parseformula("p"), parseformula("q")), IH4) == true
@test hybridalphasat(FiniteIndexTruth(3), →(parseformula("p"), parseformula("q")), IH4) == true
@test hybridalphasat(FiniteIndexTruth(4), →(parseformula("p"), parseformula("q")), IH4) == true
@test hybridalphasat(FiniteIndexTruth(1), →(parseformula("p"), parseformula("q")), IH4) == true

@test hybridalphasat(FiniteIndexTruth(2), →(parseformula("q"), parseformula("p")), IH4) == true
@test hybridalphasat(FiniteIndexTruth(3), →(parseformula("q"), parseformula("p")), IH4) == true
@test hybridalphasat(FiniteIndexTruth(4), →(parseformula("q"), parseformula("p")), IH4) == true
@test hybridalphasat(FiniteIndexTruth(1), →(parseformula("q"), parseformula("p")), IH4) == true
