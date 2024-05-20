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
        @test alphasat(i, j, FiniteHeytingAlgebra(H4)) == alphaprove(i, j, FiniteHeytingAlgebra(H4))
        for k ∈ getdomain(FiniteHeytingAlgebra(H4))
            # println("$i\t$j\t$k")
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

############################################################################################
#### Old and new rules compatibility #######################################################
############################################################################################

for i ∈ getdomain(H9)
    for j ∈ getdomain(H9)
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
        for k ∈ getdomain(H9)
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

using Random

BASE_MANY_VALUED_CONNECTIVES = [∨, ∧, →]
BaseManyValuedConnectives = Union{typeof.(BASE_MANY_VALUED_CONNECTIVES)...}

myalphabet = Atom.(["p"])

# TODO: test with H9
# for height in 1:4
#     for i in 1:1000
#         @test alphaprove(
#         rand(MersenneTwister(i), getdomain(H4)),
#         randformula(MersenneTwister(i), height, myalphabet, BASE_MANY_VALUED_CONNECTIVES),
#         FiniteHeytingAlgebra(H4),
#         oldrule=false,
#         timeout=600
#     ) == alphaprove(
#         rand(MersenneTwister(i), getdomain(H4)),
#         randformula(MersenneTwister(i), height, myalphabet, BASE_MANY_VALUED_CONNECTIVES),
#         FiniteHeytingAlgebra(H4),
#         oldrule=true,
#         timeout=600
#     )
#     end
# end
