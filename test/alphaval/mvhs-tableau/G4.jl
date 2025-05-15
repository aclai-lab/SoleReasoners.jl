################################################################################
#### G4 ########################################################################
################################################################################

using SoleLogics.ManyValuedLogics: G4, getdomain
using SoleLogics.ManyValuedLogics: α, β

################################################################################
## Base cases ##################################################################
################################################################################

for i ∈ getdomain(G4)
    for j ∈ getdomain(G4)
        @test alphaval(
            MVHSTableau,
            i,
            j,
        G4) == alphasat(MVHSTableau, i, j, G4)
        for k ∈ getdomain(G4)
            @test alphaval(
                MVHSTableau,
                i,
                ∨(j,k),
                G4
            ) == alphasat(MVHSTableau, i, ∨(j,k), G4)
            @test alphaval(
                MVHSTableau,
                i,
                ∧(j,k),
                G4
            ) == alphasat(MVHSTableau, i, ∧(j,k), G4)
            @test alphaval(
                MVHSTableau,
                i,
                →(j,k),
                G4
            ) == alphasat(MVHSTableau, i, →(j,k), G4)
        end
    end
end

@test alphaval(MVHSTableau, ⊥, parseformula("p"), G4) == true
@test alphaval(MVHSTableau, α, parseformula("p"), G4) == false
@test alphaval(MVHSTableau, β, parseformula("p"), G4) == false
@test alphaval(MVHSTableau, ⊤, parseformula("p"), G4) == false

################################################################################
## (Strong) disjunction ########################################################
################################################################################

@test alphaval(MVHSTableau, ⊥, ∨(parseformula("p"), ⊥), G4) == true
@test alphaval(MVHSTableau, ⊥, ∨(parseformula("p"), α), G4) == true
@test alphaval(MVHSTableau, ⊥, ∨(parseformula("p"), β), G4) == true
@test alphaval(MVHSTableau, ⊥, ∨(parseformula("p"), ⊤), G4) == true
@test alphaval(MVHSTableau, α, ∨(parseformula("p"), ⊥), G4) == false
@test alphaval(MVHSTableau, α, ∨(parseformula("p"), α), G4) == true
@test alphaval(MVHSTableau, α, ∨(parseformula("p"), β), G4) == true
@test alphaval(MVHSTableau, α, ∨(parseformula("p"), ⊤), G4) == true
@test alphaval(MVHSTableau, β, ∨(parseformula("p"), ⊥), G4) == false
@test alphaval(MVHSTableau, β, ∨(parseformula("p"), α), G4) == false
@test alphaval(MVHSTableau, β, ∨(parseformula("p"), β), G4) == true
@test alphaval(MVHSTableau, β, ∨(parseformula("p"), ⊤), G4) == true
@test alphaval(MVHSTableau, ⊤, ∨(parseformula("p"), ⊥), G4) == false
@test alphaval(MVHSTableau, ⊤, ∨(parseformula("p"), α), G4) == false
@test alphaval(MVHSTableau, ⊤, ∨(parseformula("p"), β), G4) == false
@test alphaval(MVHSTableau, ⊤, ∨(parseformula("p"), ⊤), G4) == true

@test alphaval(MVHSTableau, ⊥, ∨(⊥, parseformula("p")), G4) == true
@test alphaval(MVHSTableau, ⊥, ∨(α, parseformula("p")), G4) == true 
@test alphaval(MVHSTableau, ⊥, ∨(β, parseformula("p")), G4) == true 
@test alphaval(MVHSTableau, ⊥, ∨(⊤, parseformula("p")), G4) == true 
@test alphaval(MVHSTableau, α, ∨(⊥, parseformula("p")), G4) == false
@test alphaval(MVHSTableau, α, ∨(α, parseformula("p")), G4) == true 
@test alphaval(MVHSTableau, α, ∨(β, parseformula("p")), G4) == true 
@test alphaval(MVHSTableau, α, ∨(⊤, parseformula("p")), G4) == true 
@test alphaval(MVHSTableau, β, ∨(⊥, parseformula("p")), G4) == false 
@test alphaval(MVHSTableau, β, ∨(α, parseformula("p")), G4) == false 
@test alphaval(MVHSTableau, β, ∨(β, parseformula("p")), G4) == true 
@test alphaval(MVHSTableau, β, ∨(⊤, parseformula("p")), G4) == true 
@test alphaval(MVHSTableau, ⊤, ∨(⊥, parseformula("p")), G4) == false 
@test alphaval(MVHSTableau, ⊤, ∨(α, parseformula("p")), G4) == false 
@test alphaval(MVHSTableau, ⊤, ∨(β, parseformula("p")), G4) == false 
@test alphaval(MVHSTableau, ⊤, ∨(⊤, parseformula("p")), G4) == true 

@test alphaval(
    MVHSTableau,
    ⊥,
    ∨(parseformula("p"), parseformula("p")),
    G4
) == true
@test alphaval(
    MVHSTableau,
    α,
    ∨(parseformula("p"), parseformula("p")),
    G4
) == false
@test alphaval(
    MVHSTableau,
    β,
    ∨(parseformula("p"), parseformula("p")),
    G4
) == false
@test alphaval(
    MVHSTableau,
    ⊤,
    ∨(parseformula("p"), parseformula("p")),
    G4
) == false

@test alphaval(
    MVHSTableau,
    ⊥,
    ∨(parseformula("p"), parseformula("q")),
    G4
) == true
@test alphaval(
    MVHSTableau,
    α,
    ∨(parseformula("p"), parseformula("q")),
    G4
) == false
@test alphaval(
    MVHSTableau,
    β,
    ∨(parseformula("p"), parseformula("q")),
    G4
) == false
@test alphaval(
    MVHSTableau,
    ⊤,
    ∨(parseformula("p"), parseformula("q")),
    G4
) == false

@test alphaval(
    MVHSTableau,
    ⊥,
    ∨(parseformula("q"), parseformula("p")),
    G4
) == true
@test alphaval(
    MVHSTableau,
    α,
    ∨(parseformula("q"), parseformula("p")),
    G4
) == false
@test alphaval(
    MVHSTableau,
    β,
    ∨(parseformula("q"), parseformula("p")),
    G4
) == false
@test alphaval(
    MVHSTableau,
    ⊤,
    ∨(parseformula("q"), parseformula("p")),
    G4
) == false

################################################################################
## (Strong) conjunction ########################################################
################################################################################

@test alphaval(MVHSTableau, ⊥, ∧(parseformula("p"), ⊥), G4) == true
@test alphaval(MVHSTableau, ⊥, ∧(parseformula("p"), α), G4) == true
@test alphaval(MVHSTableau, ⊥, ∧(parseformula("p"), β), G4) == true
@test alphaval(MVHSTableau, ⊥, ∧(parseformula("p"), ⊤), G4) == true
@test alphaval(MVHSTableau, α, ∧(parseformula("p"), ⊥), G4) == false
@test alphaval(MVHSTableau, α, ∧(parseformula("p"), α), G4) == false
@test alphaval(MVHSTableau, α, ∧(parseformula("p"), β), G4) == false
@test alphaval(MVHSTableau, α, ∧(parseformula("p"), ⊤), G4) == false
@test alphaval(MVHSTableau, β, ∧(parseformula("p"), ⊥), G4) == false
@test alphaval(MVHSTableau, β, ∧(parseformula("p"), α), G4) == false
@test alphaval(MVHSTableau, β, ∧(parseformula("p"), β), G4) == false
@test alphaval(MVHSTableau, β, ∧(parseformula("p"), ⊤), G4) == false
@test alphaval(MVHSTableau, ⊤, ∧(parseformula("p"), ⊥), G4) == false
@test alphaval(MVHSTableau, ⊤, ∧(parseformula("p"), α), G4) == false
@test alphaval(MVHSTableau, ⊤, ∧(parseformula("p"), β), G4) == false
@test alphaval(MVHSTableau, ⊤, ∧(parseformula("p"), ⊤), G4) == false

@test alphaval(MVHSTableau, ⊥, ∧(⊥, parseformula("p")), G4) == true 
@test alphaval(MVHSTableau, ⊥, ∧(α, parseformula("p")), G4) == true 
@test alphaval(MVHSTableau, ⊥, ∧(β, parseformula("p")), G4) == true 
@test alphaval(MVHSTableau, ⊥, ∧(⊤, parseformula("p")), G4) == true 
@test alphaval(MVHSTableau, α, ∧(⊥, parseformula("p")), G4) == false
@test alphaval(MVHSTableau, α, ∧(α, parseformula("p")), G4) == false 
@test alphaval(MVHSTableau, α, ∧(β, parseformula("p")), G4) == false 
@test alphaval(MVHSTableau, α, ∧(⊤, parseformula("p")), G4) == false 
@test alphaval(MVHSTableau, β, ∧(⊥, parseformula("p")), G4) == false 
@test alphaval(MVHSTableau, β, ∧(α, parseformula("p")), G4) == false 
@test alphaval(MVHSTableau, β, ∧(β, parseformula("p")), G4) == false 
@test alphaval(MVHSTableau, β, ∧(⊤, parseformula("p")), G4) == false 
@test alphaval(MVHSTableau, ⊤, ∧(⊥, parseformula("p")), G4) == false 
@test alphaval(MVHSTableau, ⊤, ∧(α, parseformula("p")), G4) == false 
@test alphaval(MVHSTableau, ⊤, ∧(β, parseformula("p")), G4) == false 
@test alphaval(MVHSTableau, ⊤, ∧(⊤, parseformula("p")), G4) == false 

@test alphaval(
    MVHSTableau,
    ⊥,
    ∧(parseformula("p"), parseformula("p")),
    G4
) == true
@test alphaval(
    MVHSTableau,
    α,
    ∧(parseformula("p"), parseformula("p")),
    G4
) == false
@test alphaval(
    MVHSTableau,
    β,
    ∧(parseformula("p"), parseformula("p")),
    G4
) == false
@test alphaval(
    MVHSTableau,
    ⊤,
    ∧(parseformula("p"), parseformula("p")),
    G4
) == false

@test alphaval(
    MVHSTableau,
    ⊥,
    ∧(parseformula("p"), parseformula("q")),
    G4
) == true
@test alphaval(
    MVHSTableau,
    α,
    ∧(parseformula("p"), parseformula("q")),
    G4
) == false
@test alphaval(
    MVHSTableau,
    β,
    ∧(parseformula("p"), parseformula("q")),
    G4
) == false
@test alphaval(
    MVHSTableau,
    ⊤,
    ∧(parseformula("p"), parseformula("q")),
    G4
) == false

@test alphaval(
    MVHSTableau,
    ⊥,
    ∧(parseformula("q"), parseformula("p")),
    G4
) == true
@test alphaval(
    MVHSTableau,
    α,
    ∧(parseformula("q"), parseformula("p")),
    G4
) == false
@test alphaval(
    MVHSTableau,
    β,
    ∧(parseformula("q"), parseformula("p")),
    G4
) == false
@test alphaval(
    MVHSTableau,
    ⊤,
    ∧(parseformula("q"), parseformula("p")),
    G4
) == false

################################################################################
## Implication #################################################################
################################################################################

@test alphaval(MVHSTableau, ⊥, →(parseformula("p"), ⊥), G4) == true
@test alphaval(MVHSTableau, ⊥, →(parseformula("p"), α), G4) == true
@test alphaval(MVHSTableau, ⊥, →(parseformula("p"), β), G4) == true
@test alphaval(MVHSTableau, ⊥, →(parseformula("p"), ⊤), G4) == true
@test alphaval(MVHSTableau, α, →(parseformula("p"), ⊥), G4) == false
@test alphaval(MVHSTableau, α, →(parseformula("p"), α), G4) == true
@test alphaval(MVHSTableau, α, →(parseformula("p"), β), G4) == true
@test alphaval(MVHSTableau, α, →(parseformula("p"), ⊤), G4) == true
@test alphaval(MVHSTableau, β, →(parseformula("p"), ⊥), G4) == false
@test alphaval(MVHSTableau, β, →(parseformula("p"), α), G4) == false
@test alphaval(MVHSTableau, β, →(parseformula("p"), β), G4) == true
@test alphaval(MVHSTableau, β, →(parseformula("p"), ⊤), G4) == true
@test alphaval(MVHSTableau, ⊤, →(parseformula("p"), ⊥), G4) == false
@test alphaval(MVHSTableau, ⊤, →(parseformula("p"), α), G4) == false
@test alphaval(MVHSTableau, ⊤, →(parseformula("p"), β), G4) == false
@test alphaval(MVHSTableau, ⊤, →(parseformula("p"), ⊤), G4) == true

@test alphaval(MVHSTableau, ⊥, →(⊥, parseformula("p")), G4) == true
@test alphaval(MVHSTableau, ⊥, →(α, parseformula("p")), G4) == true
@test alphaval(MVHSTableau, ⊥, →(β, parseformula("p")), G4) == true
@test alphaval(MVHSTableau, ⊥, →(⊤, parseformula("p")), G4) == true
@test alphaval(MVHSTableau, α, →(⊥, parseformula("p")), G4) == true
@test alphaval(MVHSTableau, α, →(α, parseformula("p")), G4) == false
@test alphaval(MVHSTableau, α, →(β, parseformula("p")), G4) == false
@test alphaval(MVHSTableau, α, →(⊤, parseformula("p")), G4) == false
@test alphaval(MVHSTableau, β, →(⊥, parseformula("p")), G4) == true
@test alphaval(MVHSTableau, β, →(α, parseformula("p")), G4) == false
@test alphaval(MVHSTableau, β, →(β, parseformula("p")), G4) == false
@test alphaval(MVHSTableau, β, →(⊤, parseformula("p")), G4) == false
@test alphaval(MVHSTableau, ⊤, →(⊥, parseformula("p")), G4) == true
@test alphaval(MVHSTableau, ⊤, →(α, parseformula("p")), G4) == false
@test alphaval(MVHSTableau, ⊤, →(β, parseformula("p")), G4) == false
@test alphaval(MVHSTableau, ⊤, →(⊤, parseformula("p")), G4) == false

@test alphaval(
    MVHSTableau,
    ⊥,
    →(parseformula("p"), parseformula("p")),
    G4
) == true
@test alphaval(
    MVHSTableau,
    α,
    →(parseformula("p"), parseformula("p")),
    G4
) == true
@test alphaval(
    MVHSTableau,
    β,
    →(parseformula("p"), parseformula("p")),
    G4
) == true
@test alphaval(
    MVHSTableau,
    ⊤,
    →(parseformula("p"), parseformula("p")),
    G4
) == true

@test alphaval(
    MVHSTableau,
    ⊥,
    →(parseformula("p"), parseformula("q")),
    G4
) == true
@test alphaval(
    MVHSTableau,
    α,
    →(parseformula("p"), parseformula("q")),
    G4
) == false
@test alphaval(
    MVHSTableau,
    β,
    →(parseformula("p"), parseformula("q")),
    G4
) == false
@test alphaval(
    MVHSTableau,
    ⊤,
    →(parseformula("p"), parseformula("q")),
    G4
) == false

@test alphaval(
    MVHSTableau,
    ⊥,
    →(parseformula("q"), parseformula("p")),
    G4
) == true
@test alphaval(
    MVHSTableau,
    α,
    →(parseformula("q"), parseformula("p")),
    G4
) == false
@test alphaval(
    MVHSTableau,
    β,
    →(parseformula("q"), parseformula("p")),
    G4
) == false
@test alphaval(
    MVHSTableau,
    ⊤,
    →(parseformula("q"), parseformula("p")),
    G4
) == false
