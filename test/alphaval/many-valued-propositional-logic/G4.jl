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
            MVLTLFPTableau,
            i,
            j,
        G4) == alphasat(MVLTLFPTableau, i, j, G4)
        for k ∈ getdomain(G4)
            @test alphaval(
                MVLTLFPTableau,
                i,
                ∨(j,k),
                G4
            ) == alphasat(MVLTLFPTableau, i, ∨(j,k), G4)
            @test alphaval(
                MVLTLFPTableau,
                i,
                ∧(j,k),
                G4
            ) == alphasat(MVLTLFPTableau, i, ∧(j,k), G4)
            @test alphaval(
                MVLTLFPTableau,
                i,
                →(j,k),
                G4
            ) == alphasat(MVLTLFPTableau, i, →(j,k), G4)
        end
    end
end

@test alphaval(MVLTLFPTableau, ⊥, parseformula("p"), G4) == true
@test alphaval(MVLTLFPTableau, α, parseformula("p"), G4) == false
@test alphaval(MVLTLFPTableau, β, parseformula("p"), G4) == false
@test alphaval(MVLTLFPTableau, ⊤, parseformula("p"), G4) == false

################################################################################
## (Strong) disjunction ########################################################
################################################################################

@test alphaval(MVLTLFPTableau, ⊥, ∨(parseformula("p"), ⊥), G4) == true
@test alphaval(MVLTLFPTableau, ⊥, ∨(parseformula("p"), α), G4) == true
@test alphaval(MVLTLFPTableau, ⊥, ∨(parseformula("p"), β), G4) == true
@test alphaval(MVLTLFPTableau, ⊥, ∨(parseformula("p"), ⊤), G4) == true
@test alphaval(MVLTLFPTableau, α, ∨(parseformula("p"), ⊥), G4) == false
@test alphaval(MVLTLFPTableau, α, ∨(parseformula("p"), α), G4) == true
@test alphaval(MVLTLFPTableau, α, ∨(parseformula("p"), β), G4) == true
@test alphaval(MVLTLFPTableau, α, ∨(parseformula("p"), ⊤), G4) == true
@test alphaval(MVLTLFPTableau, β, ∨(parseformula("p"), ⊥), G4) == false
@test alphaval(MVLTLFPTableau, β, ∨(parseformula("p"), α), G4) == false
@test alphaval(MVLTLFPTableau, β, ∨(parseformula("p"), β), G4) == true
@test alphaval(MVLTLFPTableau, β, ∨(parseformula("p"), ⊤), G4) == true
@test alphaval(MVLTLFPTableau, ⊤, ∨(parseformula("p"), ⊥), G4) == false
@test alphaval(MVLTLFPTableau, ⊤, ∨(parseformula("p"), α), G4) == false
@test alphaval(MVLTLFPTableau, ⊤, ∨(parseformula("p"), β), G4) == false
@test alphaval(MVLTLFPTableau, ⊤, ∨(parseformula("p"), ⊤), G4) == true

@test alphaval(MVLTLFPTableau, ⊥, ∨(⊥, parseformula("p")), G4) == true
@test alphaval(MVLTLFPTableau, ⊥, ∨(α, parseformula("p")), G4) == true 
@test alphaval(MVLTLFPTableau, ⊥, ∨(β, parseformula("p")), G4) == true 
@test alphaval(MVLTLFPTableau, ⊥, ∨(⊤, parseformula("p")), G4) == true 
@test alphaval(MVLTLFPTableau, α, ∨(⊥, parseformula("p")), G4) == false
@test alphaval(MVLTLFPTableau, α, ∨(α, parseformula("p")), G4) == true 
@test alphaval(MVLTLFPTableau, α, ∨(β, parseformula("p")), G4) == true 
@test alphaval(MVLTLFPTableau, α, ∨(⊤, parseformula("p")), G4) == true 
@test alphaval(MVLTLFPTableau, β, ∨(⊥, parseformula("p")), G4) == false 
@test alphaval(MVLTLFPTableau, β, ∨(α, parseformula("p")), G4) == false 
@test alphaval(MVLTLFPTableau, β, ∨(β, parseformula("p")), G4) == true 
@test alphaval(MVLTLFPTableau, β, ∨(⊤, parseformula("p")), G4) == true 
@test alphaval(MVLTLFPTableau, ⊤, ∨(⊥, parseformula("p")), G4) == false 
@test alphaval(MVLTLFPTableau, ⊤, ∨(α, parseformula("p")), G4) == false 
@test alphaval(MVLTLFPTableau, ⊤, ∨(β, parseformula("p")), G4) == false 
@test alphaval(MVLTLFPTableau, ⊤, ∨(⊤, parseformula("p")), G4) == true 

@test alphaval(
    MVLTLFPTableau,
    ⊥,
    ∨(parseformula("p"), parseformula("p")),
    G4
) == true
@test alphaval(
    MVLTLFPTableau,
    α,
    ∨(parseformula("p"), parseformula("p")),
    G4
) == false
@test alphaval(
    MVLTLFPTableau,
    β,
    ∨(parseformula("p"), parseformula("p")),
    G4
) == false
@test alphaval(
    MVLTLFPTableau,
    ⊤,
    ∨(parseformula("p"), parseformula("p")),
    G4
) == false

@test alphaval(
    MVLTLFPTableau,
    ⊥,
    ∨(parseformula("p"), parseformula("q")),
    G4
) == true
@test alphaval(
    MVLTLFPTableau,
    α,
    ∨(parseformula("p"), parseformula("q")),
    G4
) == false
@test alphaval(
    MVLTLFPTableau,
    β,
    ∨(parseformula("p"), parseformula("q")),
    G4
) == false
@test alphaval(
    MVLTLFPTableau,
    ⊤,
    ∨(parseformula("p"), parseformula("q")),
    G4
) == false

@test alphaval(
    MVLTLFPTableau,
    ⊥,
    ∨(parseformula("q"), parseformula("p")),
    G4
) == true
@test alphaval(
    MVLTLFPTableau,
    α,
    ∨(parseformula("q"), parseformula("p")),
    G4
) == false
@test alphaval(
    MVLTLFPTableau,
    β,
    ∨(parseformula("q"), parseformula("p")),
    G4
) == false
@test alphaval(
    MVLTLFPTableau,
    ⊤,
    ∨(parseformula("q"), parseformula("p")),
    G4
) == false

################################################################################
## (Strong) conjunction ########################################################
################################################################################

@test alphaval(MVLTLFPTableau, ⊥, ∧(parseformula("p"), ⊥), G4) == true
@test alphaval(MVLTLFPTableau, ⊥, ∧(parseformula("p"), α), G4) == true
@test alphaval(MVLTLFPTableau, ⊥, ∧(parseformula("p"), β), G4) == true
@test alphaval(MVLTLFPTableau, ⊥, ∧(parseformula("p"), ⊤), G4) == true
@test alphaval(MVLTLFPTableau, α, ∧(parseformula("p"), ⊥), G4) == false
@test alphaval(MVLTLFPTableau, α, ∧(parseformula("p"), α), G4) == false
@test alphaval(MVLTLFPTableau, α, ∧(parseformula("p"), β), G4) == false
@test alphaval(MVLTLFPTableau, α, ∧(parseformula("p"), ⊤), G4) == false
@test alphaval(MVLTLFPTableau, β, ∧(parseformula("p"), ⊥), G4) == false
@test alphaval(MVLTLFPTableau, β, ∧(parseformula("p"), α), G4) == false
@test alphaval(MVLTLFPTableau, β, ∧(parseformula("p"), β), G4) == false
@test alphaval(MVLTLFPTableau, β, ∧(parseformula("p"), ⊤), G4) == false
@test alphaval(MVLTLFPTableau, ⊤, ∧(parseformula("p"), ⊥), G4) == false
@test alphaval(MVLTLFPTableau, ⊤, ∧(parseformula("p"), α), G4) == false
@test alphaval(MVLTLFPTableau, ⊤, ∧(parseformula("p"), β), G4) == false
@test alphaval(MVLTLFPTableau, ⊤, ∧(parseformula("p"), ⊤), G4) == false

@test alphaval(MVLTLFPTableau, ⊥, ∧(⊥, parseformula("p")), G4) == true 
@test alphaval(MVLTLFPTableau, ⊥, ∧(α, parseformula("p")), G4) == true 
@test alphaval(MVLTLFPTableau, ⊥, ∧(β, parseformula("p")), G4) == true 
@test alphaval(MVLTLFPTableau, ⊥, ∧(⊤, parseformula("p")), G4) == true 
@test alphaval(MVLTLFPTableau, α, ∧(⊥, parseformula("p")), G4) == false
@test alphaval(MVLTLFPTableau, α, ∧(α, parseformula("p")), G4) == false 
@test alphaval(MVLTLFPTableau, α, ∧(β, parseformula("p")), G4) == false 
@test alphaval(MVLTLFPTableau, α, ∧(⊤, parseformula("p")), G4) == false 
@test alphaval(MVLTLFPTableau, β, ∧(⊥, parseformula("p")), G4) == false 
@test alphaval(MVLTLFPTableau, β, ∧(α, parseformula("p")), G4) == false 
@test alphaval(MVLTLFPTableau, β, ∧(β, parseformula("p")), G4) == false 
@test alphaval(MVLTLFPTableau, β, ∧(⊤, parseformula("p")), G4) == false 
@test alphaval(MVLTLFPTableau, ⊤, ∧(⊥, parseformula("p")), G4) == false 
@test alphaval(MVLTLFPTableau, ⊤, ∧(α, parseformula("p")), G4) == false 
@test alphaval(MVLTLFPTableau, ⊤, ∧(β, parseformula("p")), G4) == false 
@test alphaval(MVLTLFPTableau, ⊤, ∧(⊤, parseformula("p")), G4) == false 

@test alphaval(
    MVLTLFPTableau,
    ⊥,
    ∧(parseformula("p"), parseformula("p")),
    G4
) == true
@test alphaval(
    MVLTLFPTableau,
    α,
    ∧(parseformula("p"), parseformula("p")),
    G4
) == false
@test alphaval(
    MVLTLFPTableau,
    β,
    ∧(parseformula("p"), parseformula("p")),
    G4
) == false
@test alphaval(
    MVLTLFPTableau,
    ⊤,
    ∧(parseformula("p"), parseformula("p")),
    G4
) == false

@test alphaval(
    MVLTLFPTableau,
    ⊥,
    ∧(parseformula("p"), parseformula("q")),
    G4
) == true
@test alphaval(
    MVLTLFPTableau,
    α,
    ∧(parseformula("p"), parseformula("q")),
    G4
) == false
@test alphaval(
    MVLTLFPTableau,
    β,
    ∧(parseformula("p"), parseformula("q")),
    G4
) == false
@test alphaval(
    MVLTLFPTableau,
    ⊤,
    ∧(parseformula("p"), parseformula("q")),
    G4
) == false

@test alphaval(
    MVLTLFPTableau,
    ⊥,
    ∧(parseformula("q"), parseformula("p")),
    G4
) == true
@test alphaval(
    MVLTLFPTableau,
    α,
    ∧(parseformula("q"), parseformula("p")),
    G4
) == false
@test alphaval(
    MVLTLFPTableau,
    β,
    ∧(parseformula("q"), parseformula("p")),
    G4
) == false
@test alphaval(
    MVLTLFPTableau,
    ⊤,
    ∧(parseformula("q"), parseformula("p")),
    G4
) == false

################################################################################
## Implication #################################################################
################################################################################

@test alphaval(MVLTLFPTableau, ⊥, →(parseformula("p"), ⊥), G4) == true
@test alphaval(MVLTLFPTableau, ⊥, →(parseformula("p"), α), G4) == true
@test alphaval(MVLTLFPTableau, ⊥, →(parseformula("p"), β), G4) == true
@test alphaval(MVLTLFPTableau, ⊥, →(parseformula("p"), ⊤), G4) == true
@test alphaval(MVLTLFPTableau, α, →(parseformula("p"), ⊥), G4) == false
@test alphaval(MVLTLFPTableau, α, →(parseformula("p"), α), G4) == true
@test alphaval(MVLTLFPTableau, α, →(parseformula("p"), β), G4) == true
@test alphaval(MVLTLFPTableau, α, →(parseformula("p"), ⊤), G4) == true
@test alphaval(MVLTLFPTableau, β, →(parseformula("p"), ⊥), G4) == false
@test alphaval(MVLTLFPTableau, β, →(parseformula("p"), α), G4) == false
@test alphaval(MVLTLFPTableau, β, →(parseformula("p"), β), G4) == true
@test alphaval(MVLTLFPTableau, β, →(parseformula("p"), ⊤), G4) == true
@test alphaval(MVLTLFPTableau, ⊤, →(parseformula("p"), ⊥), G4) == false
@test alphaval(MVLTLFPTableau, ⊤, →(parseformula("p"), α), G4) == false
@test alphaval(MVLTLFPTableau, ⊤, →(parseformula("p"), β), G4) == false
@test alphaval(MVLTLFPTableau, ⊤, →(parseformula("p"), ⊤), G4) == true

@test alphaval(MVLTLFPTableau, ⊥, →(⊥, parseformula("p")), G4) == true
@test alphaval(MVLTLFPTableau, ⊥, →(α, parseformula("p")), G4) == true
@test alphaval(MVLTLFPTableau, ⊥, →(β, parseformula("p")), G4) == true
@test alphaval(MVLTLFPTableau, ⊥, →(⊤, parseformula("p")), G4) == true
@test alphaval(MVLTLFPTableau, α, →(⊥, parseformula("p")), G4) == true
@test alphaval(MVLTLFPTableau, α, →(α, parseformula("p")), G4) == false
@test alphaval(MVLTLFPTableau, α, →(β, parseformula("p")), G4) == false
@test alphaval(MVLTLFPTableau, α, →(⊤, parseformula("p")), G4) == false
@test alphaval(MVLTLFPTableau, β, →(⊥, parseformula("p")), G4) == true
@test alphaval(MVLTLFPTableau, β, →(α, parseformula("p")), G4) == false
@test alphaval(MVLTLFPTableau, β, →(β, parseformula("p")), G4) == false
@test alphaval(MVLTLFPTableau, β, →(⊤, parseformula("p")), G4) == false
@test alphaval(MVLTLFPTableau, ⊤, →(⊥, parseformula("p")), G4) == true
@test alphaval(MVLTLFPTableau, ⊤, →(α, parseformula("p")), G4) == false
@test alphaval(MVLTLFPTableau, ⊤, →(β, parseformula("p")), G4) == false
@test alphaval(MVLTLFPTableau, ⊤, →(⊤, parseformula("p")), G4) == false

@test alphaval(
    MVLTLFPTableau,
    ⊥,
    →(parseformula("p"), parseformula("p")),
    G4
) == true
@test alphaval(
    MVLTLFPTableau,
    α,
    →(parseformula("p"), parseformula("p")),
    G4
) == true
@test alphaval(
    MVLTLFPTableau,
    β,
    →(parseformula("p"), parseformula("p")),
    G4
) == true
@test alphaval(
    MVLTLFPTableau,
    ⊤,
    →(parseformula("p"), parseformula("p")),
    G4
) == true

@test alphaval(
    MVLTLFPTableau,
    ⊥,
    →(parseformula("p"), parseformula("q")),
    G4
) == true
@test alphaval(
    MVLTLFPTableau,
    α,
    →(parseformula("p"), parseformula("q")),
    G4
) == false
@test alphaval(
    MVLTLFPTableau,
    β,
    →(parseformula("p"), parseformula("q")),
    G4
) == false
@test alphaval(
    MVLTLFPTableau,
    ⊤,
    →(parseformula("p"), parseformula("q")),
    G4
) == false

@test alphaval(
    MVLTLFPTableau,
    ⊥,
    →(parseformula("q"), parseformula("p")),
    G4
) == true
@test alphaval(
    MVLTLFPTableau,
    α,
    →(parseformula("q"), parseformula("p")),
    G4
) == false
@test alphaval(
    MVLTLFPTableau,
    β,
    →(parseformula("q"), parseformula("p")),
    G4
) == false
@test alphaval(
    MVLTLFPTableau,
    ⊤,
    →(parseformula("q"), parseformula("p")),
    G4
) == false
