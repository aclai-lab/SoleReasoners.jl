############################################################################################
#### G4 ####################################################################################
############################################################################################

using SoleLogics.ManyValuedLogics: G4
using SoleLogics.ManyValuedLogics: α, β

############################################################################################
## Base cases ##############################################################################
############################################################################################

# for i ∈ getdomain(G4)
#     for j ∈ getdomain(G4)
#         @test alphasat(i, j, G4) == hybridalphaprove(i, j, G4)
#         for k ∈ getdomain(G4)
#             @test alphasat(i, ∨(j,k), G4) == hybridalphaprove(i, ∨(j,k), G4)
#             @test alphasat(i, ∧(j,k), G4) == hybridalphaprove(i, ∧(j,k), G4)
#             @test alphasat(i, →(j,k), G4) == hybridalphaprove(i, →(j,k), G4)
#         end
#     end
# end

# @test hybridalphaprove(⊥, parseformula("p"), G4) == true
# @test hybridalphaprove(α, parseformula("p"), G4) == false
# @test hybridalphaprove(β, parseformula("p"), G4) == false
# @test hybridalphaprove(⊤, parseformula("p"), G4) == false

@test true == false