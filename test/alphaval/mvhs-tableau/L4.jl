################################################################################
#### Ł4 ########################################################################
################################################################################

using SoleLogics.ManyValuedLogics: Ł4, getdomain
using SoleLogics.ManyValuedLogics: α, β

################################################################################
## Base cases ##################################################################
################################################################################

for i ∈ getdomain(Ł4)
    for j ∈ getdomain(Ł4)
        @test alphaval(
            MVHSTableau,
            i,
            j,
        Ł4) == alphasat(MVHSTableau, i, j, Ł4)
        for k ∈ getdomain(Ł4)
            @test alphaval(
                MVHSTableau,
                i,
                ∨(j,k),
                Ł4
            ) == alphasat(MVHSTableau, i, ∨(j,k), Ł4)
            @test alphaval(
                MVHSTableau,
                i,
                ∧(j,k),
                Ł4
            ) == alphasat(MVHSTableau, i, ∧(j,k), Ł4)
            @test alphaval(
                MVHSTableau,
                i,
                →(j,k),
                Ł4
            ) == alphasat(MVHSTableau, i, →(j,k), Ł4)
        end
    end
end

@test alphaval(MVHSTableau, ⊥, parseformula("p"), Ł4) == true
@test alphaval(MVHSTableau, α, parseformula("p"), Ł4) == false
@test alphaval(MVHSTableau, β, parseformula("p"), Ł4) == false
@test alphaval(MVHSTableau, ⊤, parseformula("p"), Ł4) == false

################################################################################
## (Strong) disjunction ########################################################
################################################################################

@test alphaval(MVHSTableau, ⊥, ∨(parseformula("p"), ⊥), Ł4) == true
@test alphaval(MVHSTableau, ⊥, ∨(parseformula("p"), α), Ł4) == true
@test alphaval(MVHSTableau, ⊥, ∨(parseformula("p"), β), Ł4) == true
@test alphaval(MVHSTableau, ⊥, ∨(parseformula("p"), ⊤), Ł4) == true
@test alphaval(MVHSTableau, α, ∨(parseformula("p"), ⊥), Ł4) == false
@test alphaval(MVHSTableau, α, ∨(parseformula("p"), α), Ł4) == true
@test alphaval(MVHSTableau, α, ∨(parseformula("p"), β), Ł4) == true
@test alphaval(MVHSTableau, α, ∨(parseformula("p"), ⊤), Ł4) == true
@test alphaval(MVHSTableau, β, ∨(parseformula("p"), ⊥), Ł4) == false
@test alphaval(MVHSTableau, β, ∨(parseformula("p"), α), Ł4) == false
@test alphaval(MVHSTableau, β, ∨(parseformula("p"), β), Ł4) == true
@test alphaval(MVHSTableau, β, ∨(parseformula("p"), ⊤), Ł4) == true
@test alphaval(MVHSTableau, ⊤, ∨(parseformula("p"), ⊥), Ł4) == false
@test alphaval(MVHSTableau, ⊤, ∨(parseformula("p"), α), Ł4) == false
@test alphaval(MVHSTableau, ⊤, ∨(parseformula("p"), β), Ł4) == false
@test alphaval(MVHSTableau, ⊤, ∨(parseformula("p"), ⊤), Ł4) == true

@test alphaval(MVHSTableau, ⊥, ∨(⊥, parseformula("p")), Ł4) == true
@test alphaval(MVHSTableau, ⊥, ∨(α, parseformula("p")), Ł4) == true 
@test alphaval(MVHSTableau, ⊥, ∨(β, parseformula("p")), Ł4) == true 
@test alphaval(MVHSTableau, ⊥, ∨(⊤, parseformula("p")), Ł4) == true 
@test alphaval(MVHSTableau, α, ∨(⊥, parseformula("p")), Ł4) == false
@test alphaval(MVHSTableau, α, ∨(α, parseformula("p")), Ł4) == true 
@test alphaval(MVHSTableau, α, ∨(β, parseformula("p")), Ł4) == true 
@test alphaval(MVHSTableau, α, ∨(⊤, parseformula("p")), Ł4) == true 
@test alphaval(MVHSTableau, β, ∨(⊥, parseformula("p")), Ł4) == false 
@test alphaval(MVHSTableau, β, ∨(α, parseformula("p")), Ł4) == false 
@test alphaval(MVHSTableau, β, ∨(β, parseformula("p")), Ł4) == true 
@test alphaval(MVHSTableau, β, ∨(⊤, parseformula("p")), Ł4) == true 
@test alphaval(MVHSTableau, ⊤, ∨(⊥, parseformula("p")), Ł4) == false 
@test alphaval(MVHSTableau, ⊤, ∨(α, parseformula("p")), Ł4) == false 
@test alphaval(MVHSTableau, ⊤, ∨(β, parseformula("p")), Ł4) == false 
@test alphaval(MVHSTableau, ⊤, ∨(⊤, parseformula("p")), Ł4) == true 

@test alphaval(
    MVHSTableau,
    ⊥,
    ∨(parseformula("p"), parseformula("p")),
    Ł4
) == true
@test alphaval(
    MVHSTableau,
    α,
    ∨(parseformula("p"), parseformula("p")),
    Ł4
) == false
@test alphaval(
    MVHSTableau,
    β,
    ∨(parseformula("p"), parseformula("p")),
    Ł4
) == false
@test alphaval(
    MVHSTableau,
    ⊤,
    ∨(parseformula("p"), parseformula("p")),
    Ł4
) == false

@test alphaval(
    MVHSTableau,
    ⊥,
    ∨(parseformula("p"), parseformula("q")),
    Ł4
) == true
@test alphaval(
    MVHSTableau,
    α,
    ∨(parseformula("p"), parseformula("q")),
    Ł4
) == false
@test alphaval(
    MVHSTableau,
    β,
    ∨(parseformula("p"), parseformula("q")),
    Ł4
) == false
@test alphaval(
    MVHSTableau,
    ⊤,
    ∨(parseformula("p"), parseformula("q")),
    Ł4
) == false

@test alphaval(
    MVHSTableau,
    ⊥,
    ∨(parseformula("q"), parseformula("p")),
    Ł4
) == true
@test alphaval(
    MVHSTableau,
    α,
    ∨(parseformula("q"), parseformula("p")),
    Ł4
) == false
@test alphaval(
    MVHSTableau,
    β,
    ∨(parseformula("q"), parseformula("p")),
    Ł4
) == false
@test alphaval(
    MVHSTableau,
    ⊤,
    ∨(parseformula("q"), parseformula("p")),
    Ł4
) == false

################################################################################
## (Strong) conjunction ########################################################
################################################################################

@test alphaval(MVHSTableau, ⊥, ∧(parseformula("p"), ⊥), Ł4) == true
@test alphaval(MVHSTableau, ⊥, ∧(parseformula("p"), α), Ł4) == true
@test alphaval(MVHSTableau, ⊥, ∧(parseformula("p"), β), Ł4) == true
@test alphaval(MVHSTableau, ⊥, ∧(parseformula("p"), ⊤), Ł4) == true
@test alphaval(MVHSTableau, α, ∧(parseformula("p"), ⊥), Ł4) == false
@test alphaval(MVHSTableau, α, ∧(parseformula("p"), α), Ł4) == false
@test alphaval(MVHSTableau, α, ∧(parseformula("p"), β), Ł4) == false
@test alphaval(MVHSTableau, α, ∧(parseformula("p"), ⊤), Ł4) == false
@test alphaval(MVHSTableau, β, ∧(parseformula("p"), ⊥), Ł4) == false
@test alphaval(MVHSTableau, β, ∧(parseformula("p"), α), Ł4) == false
@test alphaval(MVHSTableau, β, ∧(parseformula("p"), β), Ł4) == false
@test alphaval(MVHSTableau, β, ∧(parseformula("p"), ⊤), Ł4) == false
@test alphaval(MVHSTableau, ⊤, ∧(parseformula("p"), ⊥), Ł4) == false
@test alphaval(MVHSTableau, ⊤, ∧(parseformula("p"), α), Ł4) == false
@test alphaval(MVHSTableau, ⊤, ∧(parseformula("p"), β), Ł4) == false
@test alphaval(MVHSTableau, ⊤, ∧(parseformula("p"), ⊤), Ł4) == false

@test alphaval(MVHSTableau, ⊥, ∧(⊥, parseformula("p")), Ł4) == true 
@test alphaval(MVHSTableau, ⊥, ∧(α, parseformula("p")), Ł4) == true 
@test alphaval(MVHSTableau, ⊥, ∧(β, parseformula("p")), Ł4) == true 
@test alphaval(MVHSTableau, ⊥, ∧(⊤, parseformula("p")), Ł4) == true 
@test alphaval(MVHSTableau, α, ∧(⊥, parseformula("p")), Ł4) == false
@test alphaval(MVHSTableau, α, ∧(α, parseformula("p")), Ł4) == false 
@test alphaval(MVHSTableau, α, ∧(β, parseformula("p")), Ł4) == false 
@test alphaval(MVHSTableau, α, ∧(⊤, parseformula("p")), Ł4) == false 
@test alphaval(MVHSTableau, β, ∧(⊥, parseformula("p")), Ł4) == false 
@test alphaval(MVHSTableau, β, ∧(α, parseformula("p")), Ł4) == false 
@test alphaval(MVHSTableau, β, ∧(β, parseformula("p")), Ł4) == false 
@test alphaval(MVHSTableau, β, ∧(⊤, parseformula("p")), Ł4) == false 
@test alphaval(MVHSTableau, ⊤, ∧(⊥, parseformula("p")), Ł4) == false 
@test alphaval(MVHSTableau, ⊤, ∧(α, parseformula("p")), Ł4) == false 
@test alphaval(MVHSTableau, ⊤, ∧(β, parseformula("p")), Ł4) == false 
@test alphaval(MVHSTableau, ⊤, ∧(⊤, parseformula("p")), Ł4) == false 

@test alphaval(
    MVHSTableau,
    ⊥,
    ∧(parseformula("p"), parseformula("p")),
    Ł4
) == true
@test alphaval(
    MVHSTableau,
    α,
    ∧(parseformula("p"), parseformula("p")),
    Ł4
) == false
@test alphaval(
    MVHSTableau,
    β,
    ∧(parseformula("p"), parseformula("p")),
    Ł4
) == false
@test alphaval(
    MVHSTableau,
    ⊤,
    ∧(parseformula("p"), parseformula("p")),
    Ł4
) == false

@test alphaval(
    MVHSTableau,
    ⊥,
    ∧(parseformula("p"), parseformula("q")),
    Ł4
) == true
@test alphaval(
    MVHSTableau,
    α,
    ∧(parseformula("p"), parseformula("q")),
    Ł4
) == false
@test alphaval(
    MVHSTableau,
    β,
    ∧(parseformula("p"), parseformula("q")),
    Ł4
) == false
@test alphaval(
    MVHSTableau,
    ⊤,
    ∧(parseformula("p"), parseformula("q")),
    Ł4
) == false

@test alphaval(
    MVHSTableau,
    ⊥,
    ∧(parseformula("q"), parseformula("p")),
    Ł4
) == true
@test alphaval(
    MVHSTableau,
    α,
    ∧(parseformula("q"), parseformula("p")),
    Ł4
) == false
@test alphaval(
    MVHSTableau,
    β,
    ∧(parseformula("q"), parseformula("p")),
    Ł4
) == false
@test alphaval(
    MVHSTableau,
    ⊤,
    ∧(parseformula("q"), parseformula("p")),
    Ł4
) == false

################################################################################
## Implication #################################################################
################################################################################

@test alphaval(MVHSTableau, ⊥, →(parseformula("p"), ⊥), Ł4) == true
@test alphaval(MVHSTableau, ⊥, →(parseformula("p"), α), Ł4) == true
@test alphaval(MVHSTableau, ⊥, →(parseformula("p"), β), Ł4) == true
@test alphaval(MVHSTableau, ⊥, →(parseformula("p"), ⊤), Ł4) == true
@test alphaval(MVHSTableau, α, →(parseformula("p"), ⊥), Ł4) == false
@test alphaval(MVHSTableau, α, →(parseformula("p"), α), Ł4) == true
@test alphaval(MVHSTableau, α, →(parseformula("p"), β), Ł4) == true
@test alphaval(MVHSTableau, α, →(parseformula("p"), ⊤), Ł4) == true
@test alphaval(MVHSTableau, β, →(parseformula("p"), ⊥), Ł4) == false
@test alphaval(MVHSTableau, β, →(parseformula("p"), α), Ł4) == false
@test alphaval(MVHSTableau, β, →(parseformula("p"), β), Ł4) == true
@test alphaval(MVHSTableau, β, →(parseformula("p"), ⊤), Ł4) == true
@test alphaval(MVHSTableau, ⊤, →(parseformula("p"), ⊥), Ł4) == false
@test alphaval(MVHSTableau, ⊤, →(parseformula("p"), α), Ł4) == false
@test alphaval(MVHSTableau, ⊤, →(parseformula("p"), β), Ł4) == false
@test alphaval(MVHSTableau, ⊤, →(parseformula("p"), ⊤), Ł4) == true

@test alphaval(MVHSTableau, ⊥, →(⊥, parseformula("p")), Ł4) == true
@test alphaval(MVHSTableau, ⊥, →(α, parseformula("p")), Ł4) == true
@test alphaval(MVHSTableau, ⊥, →(β, parseformula("p")), Ł4) == true
@test alphaval(MVHSTableau, ⊥, →(⊤, parseformula("p")), Ł4) == true
@test alphaval(MVHSTableau, α, →(⊥, parseformula("p")), Ł4) == true
@test alphaval(MVHSTableau, α, →(α, parseformula("p")), Ł4) == true
@test alphaval(MVHSTableau, α, →(β, parseformula("p")), Ł4) == true
@test alphaval(MVHSTableau, α, →(⊤, parseformula("p")), Ł4) == false
@test alphaval(MVHSTableau, β, →(⊥, parseformula("p")), Ł4) == true
@test alphaval(MVHSTableau, β, →(α, parseformula("p")), Ł4) == true
@test alphaval(MVHSTableau, β, →(β, parseformula("p")), Ł4) == false
@test alphaval(MVHSTableau, β, →(⊤, parseformula("p")), Ł4) == false
@test alphaval(MVHSTableau, ⊤, →(⊥, parseformula("p")), Ł4) == true
@test alphaval(MVHSTableau, ⊤, →(α, parseformula("p")), Ł4) == false
@test alphaval(MVHSTableau, ⊤, →(β, parseformula("p")), Ł4) == false
@test alphaval(MVHSTableau, ⊤, →(⊤, parseformula("p")), Ł4) == false

@test alphaval(
    MVHSTableau,
    ⊥,
    →(parseformula("p"), parseformula("p")),
    Ł4
) == true
@test alphaval(
    MVHSTableau,
    α,
    →(parseformula("p"), parseformula("p")),
    Ł4
) == true
@test alphaval(
    MVHSTableau,
    β,
    →(parseformula("p"), parseformula("p")),
    Ł4
) == true
@test alphaval(
    MVHSTableau,
    ⊤,
    →(parseformula("p"), parseformula("p")),
    Ł4
) == true

@test alphaval(
    MVHSTableau,
    ⊥,
    →(parseformula("p"), parseformula("q")),
    Ł4
) == true
@test alphaval(
    MVHSTableau,
    α,
    →(parseformula("p"), parseformula("q")),
    Ł4
) == false
@test alphaval(
    MVHSTableau,
    β,
    →(parseformula("p"), parseformula("q")),
    Ł4
) == false
@test alphaval(
    MVHSTableau,
    ⊤,
    →(parseformula("p"), parseformula("q")),
    Ł4
) == false

@test alphaval(
    MVHSTableau,
    ⊥,
    →(parseformula("q"), parseformula("p")),
    Ł4
) == true
@test alphaval(
    MVHSTableau,
    α,
    →(parseformula("q"), parseformula("p")),
    Ł4
) == false
@test alphaval(
    MVHSTableau,
    β,
    →(parseformula("q"), parseformula("p")),
    Ł4
) == false
@test alphaval(
    MVHSTableau,
    ⊤,
    →(parseformula("q"), parseformula("p")),
    Ł4
) == false
