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
            MVLTLFPTableau,
            i,
            j,
        Ł4) == alphasat(MVLTLFPTableau, i, j, Ł4)
        for k ∈ getdomain(Ł4)
            @test alphaval(
                MVLTLFPTableau,
                i,
                ∨(j,k),
                Ł4
            ) == alphasat(MVLTLFPTableau, i, ∨(j,k), Ł4)
            @test alphaval(
                MVLTLFPTableau,
                i,
                ∧(j,k),
                Ł4
            ) == alphasat(MVLTLFPTableau, i, ∧(j,k), Ł4)
            @test alphaval(
                MVLTLFPTableau,
                i,
                →(j,k),
                Ł4
            ) == alphasat(MVLTLFPTableau, i, →(j,k), Ł4)
        end
    end
end

@test alphaval(MVLTLFPTableau, ⊥, parseformula("p"), Ł4) == true
@test alphaval(MVLTLFPTableau, α, parseformula("p"), Ł4) == false
@test alphaval(MVLTLFPTableau, β, parseformula("p"), Ł4) == false
@test alphaval(MVLTLFPTableau, ⊤, parseformula("p"), Ł4) == false

################################################################################
## (Strong) disjunction ########################################################
################################################################################

@test alphaval(MVLTLFPTableau, ⊥, ∨(parseformula("p"), ⊥), Ł4) == true
@test alphaval(MVLTLFPTableau, ⊥, ∨(parseformula("p"), α), Ł4) == true
@test alphaval(MVLTLFPTableau, ⊥, ∨(parseformula("p"), β), Ł4) == true
@test alphaval(MVLTLFPTableau, ⊥, ∨(parseformula("p"), ⊤), Ł4) == true
@test alphaval(MVLTLFPTableau, α, ∨(parseformula("p"), ⊥), Ł4) == false
@test alphaval(MVLTLFPTableau, α, ∨(parseformula("p"), α), Ł4) == true
@test alphaval(MVLTLFPTableau, α, ∨(parseformula("p"), β), Ł4) == true
@test alphaval(MVLTLFPTableau, α, ∨(parseformula("p"), ⊤), Ł4) == true
@test alphaval(MVLTLFPTableau, β, ∨(parseformula("p"), ⊥), Ł4) == false
@test alphaval(MVLTLFPTableau, β, ∨(parseformula("p"), α), Ł4) == false
@test alphaval(MVLTLFPTableau, β, ∨(parseformula("p"), β), Ł4) == true
@test alphaval(MVLTLFPTableau, β, ∨(parseformula("p"), ⊤), Ł4) == true
@test alphaval(MVLTLFPTableau, ⊤, ∨(parseformula("p"), ⊥), Ł4) == false
@test alphaval(MVLTLFPTableau, ⊤, ∨(parseformula("p"), α), Ł4) == false
@test alphaval(MVLTLFPTableau, ⊤, ∨(parseformula("p"), β), Ł4) == false
@test alphaval(MVLTLFPTableau, ⊤, ∨(parseformula("p"), ⊤), Ł4) == true

@test alphaval(MVLTLFPTableau, ⊥, ∨(⊥, parseformula("p")), Ł4) == true
@test alphaval(MVLTLFPTableau, ⊥, ∨(α, parseformula("p")), Ł4) == true 
@test alphaval(MVLTLFPTableau, ⊥, ∨(β, parseformula("p")), Ł4) == true 
@test alphaval(MVLTLFPTableau, ⊥, ∨(⊤, parseformula("p")), Ł4) == true 
@test alphaval(MVLTLFPTableau, α, ∨(⊥, parseformula("p")), Ł4) == false
@test alphaval(MVLTLFPTableau, α, ∨(α, parseformula("p")), Ł4) == true 
@test alphaval(MVLTLFPTableau, α, ∨(β, parseformula("p")), Ł4) == true 
@test alphaval(MVLTLFPTableau, α, ∨(⊤, parseformula("p")), Ł4) == true 
@test alphaval(MVLTLFPTableau, β, ∨(⊥, parseformula("p")), Ł4) == false 
@test alphaval(MVLTLFPTableau, β, ∨(α, parseformula("p")), Ł4) == false 
@test alphaval(MVLTLFPTableau, β, ∨(β, parseformula("p")), Ł4) == true 
@test alphaval(MVLTLFPTableau, β, ∨(⊤, parseformula("p")), Ł4) == true 
@test alphaval(MVLTLFPTableau, ⊤, ∨(⊥, parseformula("p")), Ł4) == false 
@test alphaval(MVLTLFPTableau, ⊤, ∨(α, parseformula("p")), Ł4) == false 
@test alphaval(MVLTLFPTableau, ⊤, ∨(β, parseformula("p")), Ł4) == false 
@test alphaval(MVLTLFPTableau, ⊤, ∨(⊤, parseformula("p")), Ł4) == true 

@test alphaval(
    MVLTLFPTableau,
    ⊥,
    ∨(parseformula("p"), parseformula("p")),
    Ł4
) == true
@test alphaval(
    MVLTLFPTableau,
    α,
    ∨(parseformula("p"), parseformula("p")),
    Ł4
) == false
@test alphaval(
    MVLTLFPTableau,
    β,
    ∨(parseformula("p"), parseformula("p")),
    Ł4
) == false
@test alphaval(
    MVLTLFPTableau,
    ⊤,
    ∨(parseformula("p"), parseformula("p")),
    Ł4
) == false

@test alphaval(
    MVLTLFPTableau,
    ⊥,
    ∨(parseformula("p"), parseformula("q")),
    Ł4
) == true
@test alphaval(
    MVLTLFPTableau,
    α,
    ∨(parseformula("p"), parseformula("q")),
    Ł4
) == false
@test alphaval(
    MVLTLFPTableau,
    β,
    ∨(parseformula("p"), parseformula("q")),
    Ł4
) == false
@test alphaval(
    MVLTLFPTableau,
    ⊤,
    ∨(parseformula("p"), parseformula("q")),
    Ł4
) == false

@test alphaval(
    MVLTLFPTableau,
    ⊥,
    ∨(parseformula("q"), parseformula("p")),
    Ł4
) == true
@test alphaval(
    MVLTLFPTableau,
    α,
    ∨(parseformula("q"), parseformula("p")),
    Ł4
) == false
@test alphaval(
    MVLTLFPTableau,
    β,
    ∨(parseformula("q"), parseformula("p")),
    Ł4
) == false
@test alphaval(
    MVLTLFPTableau,
    ⊤,
    ∨(parseformula("q"), parseformula("p")),
    Ł4
) == false

################################################################################
## (Strong) conjunction ########################################################
################################################################################

@test alphaval(MVLTLFPTableau, ⊥, ∧(parseformula("p"), ⊥), Ł4) == true
@test alphaval(MVLTLFPTableau, ⊥, ∧(parseformula("p"), α), Ł4) == true
@test alphaval(MVLTLFPTableau, ⊥, ∧(parseformula("p"), β), Ł4) == true
@test alphaval(MVLTLFPTableau, ⊥, ∧(parseformula("p"), ⊤), Ł4) == true
@test alphaval(MVLTLFPTableau, α, ∧(parseformula("p"), ⊥), Ł4) == false
@test alphaval(MVLTLFPTableau, α, ∧(parseformula("p"), α), Ł4) == false
@test alphaval(MVLTLFPTableau, α, ∧(parseformula("p"), β), Ł4) == false
@test alphaval(MVLTLFPTableau, α, ∧(parseformula("p"), ⊤), Ł4) == false
@test alphaval(MVLTLFPTableau, β, ∧(parseformula("p"), ⊥), Ł4) == false
@test alphaval(MVLTLFPTableau, β, ∧(parseformula("p"), α), Ł4) == false
@test alphaval(MVLTLFPTableau, β, ∧(parseformula("p"), β), Ł4) == false
@test alphaval(MVLTLFPTableau, β, ∧(parseformula("p"), ⊤), Ł4) == false
@test alphaval(MVLTLFPTableau, ⊤, ∧(parseformula("p"), ⊥), Ł4) == false
@test alphaval(MVLTLFPTableau, ⊤, ∧(parseformula("p"), α), Ł4) == false
@test alphaval(MVLTLFPTableau, ⊤, ∧(parseformula("p"), β), Ł4) == false
@test alphaval(MVLTLFPTableau, ⊤, ∧(parseformula("p"), ⊤), Ł4) == false

@test alphaval(MVLTLFPTableau, ⊥, ∧(⊥, parseformula("p")), Ł4) == true 
@test alphaval(MVLTLFPTableau, ⊥, ∧(α, parseformula("p")), Ł4) == true 
@test alphaval(MVLTLFPTableau, ⊥, ∧(β, parseformula("p")), Ł4) == true 
@test alphaval(MVLTLFPTableau, ⊥, ∧(⊤, parseformula("p")), Ł4) == true 
@test alphaval(MVLTLFPTableau, α, ∧(⊥, parseformula("p")), Ł4) == false
@test alphaval(MVLTLFPTableau, α, ∧(α, parseformula("p")), Ł4) == false 
@test alphaval(MVLTLFPTableau, α, ∧(β, parseformula("p")), Ł4) == false 
@test alphaval(MVLTLFPTableau, α, ∧(⊤, parseformula("p")), Ł4) == false 
@test alphaval(MVLTLFPTableau, β, ∧(⊥, parseformula("p")), Ł4) == false 
@test alphaval(MVLTLFPTableau, β, ∧(α, parseformula("p")), Ł4) == false 
@test alphaval(MVLTLFPTableau, β, ∧(β, parseformula("p")), Ł4) == false 
@test alphaval(MVLTLFPTableau, β, ∧(⊤, parseformula("p")), Ł4) == false 
@test alphaval(MVLTLFPTableau, ⊤, ∧(⊥, parseformula("p")), Ł4) == false 
@test alphaval(MVLTLFPTableau, ⊤, ∧(α, parseformula("p")), Ł4) == false 
@test alphaval(MVLTLFPTableau, ⊤, ∧(β, parseformula("p")), Ł4) == false 
@test alphaval(MVLTLFPTableau, ⊤, ∧(⊤, parseformula("p")), Ł4) == false 

@test alphaval(
    MVLTLFPTableau,
    ⊥,
    ∧(parseformula("p"), parseformula("p")),
    Ł4
) == true
@test alphaval(
    MVLTLFPTableau,
    α,
    ∧(parseformula("p"), parseformula("p")),
    Ł4
) == false
@test alphaval(
    MVLTLFPTableau,
    β,
    ∧(parseformula("p"), parseformula("p")),
    Ł4
) == false
@test alphaval(
    MVLTLFPTableau,
    ⊤,
    ∧(parseformula("p"), parseformula("p")),
    Ł4
) == false

@test alphaval(
    MVLTLFPTableau,
    ⊥,
    ∧(parseformula("p"), parseformula("q")),
    Ł4
) == true
@test alphaval(
    MVLTLFPTableau,
    α,
    ∧(parseformula("p"), parseformula("q")),
    Ł4
) == false
@test alphaval(
    MVLTLFPTableau,
    β,
    ∧(parseformula("p"), parseformula("q")),
    Ł4
) == false
@test alphaval(
    MVLTLFPTableau,
    ⊤,
    ∧(parseformula("p"), parseformula("q")),
    Ł4
) == false

@test alphaval(
    MVLTLFPTableau,
    ⊥,
    ∧(parseformula("q"), parseformula("p")),
    Ł4
) == true
@test alphaval(
    MVLTLFPTableau,
    α,
    ∧(parseformula("q"), parseformula("p")),
    Ł4
) == false
@test alphaval(
    MVLTLFPTableau,
    β,
    ∧(parseformula("q"), parseformula("p")),
    Ł4
) == false
@test alphaval(
    MVLTLFPTableau,
    ⊤,
    ∧(parseformula("q"), parseformula("p")),
    Ł4
) == false

################################################################################
## Implication #################################################################
################################################################################

@test alphaval(MVLTLFPTableau, ⊥, →(parseformula("p"), ⊥), Ł4) == true
@test alphaval(MVLTLFPTableau, ⊥, →(parseformula("p"), α), Ł4) == true
@test alphaval(MVLTLFPTableau, ⊥, →(parseformula("p"), β), Ł4) == true
@test alphaval(MVLTLFPTableau, ⊥, →(parseformula("p"), ⊤), Ł4) == true
@test alphaval(MVLTLFPTableau, α, →(parseformula("p"), ⊥), Ł4) == false
@test alphaval(MVLTLFPTableau, α, →(parseformula("p"), α), Ł4) == true
@test alphaval(MVLTLFPTableau, α, →(parseformula("p"), β), Ł4) == true
@test alphaval(MVLTLFPTableau, α, →(parseformula("p"), ⊤), Ł4) == true
@test alphaval(MVLTLFPTableau, β, →(parseformula("p"), ⊥), Ł4) == false
@test alphaval(MVLTLFPTableau, β, →(parseformula("p"), α), Ł4) == false
@test alphaval(MVLTLFPTableau, β, →(parseformula("p"), β), Ł4) == true
@test alphaval(MVLTLFPTableau, β, →(parseformula("p"), ⊤), Ł4) == true
@test alphaval(MVLTLFPTableau, ⊤, →(parseformula("p"), ⊥), Ł4) == false
@test alphaval(MVLTLFPTableau, ⊤, →(parseformula("p"), α), Ł4) == false
@test alphaval(MVLTLFPTableau, ⊤, →(parseformula("p"), β), Ł4) == false
@test alphaval(MVLTLFPTableau, ⊤, →(parseformula("p"), ⊤), Ł4) == true

@test alphaval(MVLTLFPTableau, ⊥, →(⊥, parseformula("p")), Ł4) == true
@test alphaval(MVLTLFPTableau, ⊥, →(α, parseformula("p")), Ł4) == true
@test alphaval(MVLTLFPTableau, ⊥, →(β, parseformula("p")), Ł4) == true
@test alphaval(MVLTLFPTableau, ⊥, →(⊤, parseformula("p")), Ł4) == true
@test alphaval(MVLTLFPTableau, α, →(⊥, parseformula("p")), Ł4) == true
@test alphaval(MVLTLFPTableau, α, →(α, parseformula("p")), Ł4) == true
@test alphaval(MVLTLFPTableau, α, →(β, parseformula("p")), Ł4) == true
@test alphaval(MVLTLFPTableau, α, →(⊤, parseformula("p")), Ł4) == false
@test alphaval(MVLTLFPTableau, β, →(⊥, parseformula("p")), Ł4) == true
@test alphaval(MVLTLFPTableau, β, →(α, parseformula("p")), Ł4) == true
@test alphaval(MVLTLFPTableau, β, →(β, parseformula("p")), Ł4) == false
@test alphaval(MVLTLFPTableau, β, →(⊤, parseformula("p")), Ł4) == false
@test alphaval(MVLTLFPTableau, ⊤, →(⊥, parseformula("p")), Ł4) == true
@test alphaval(MVLTLFPTableau, ⊤, →(α, parseformula("p")), Ł4) == false
@test alphaval(MVLTLFPTableau, ⊤, →(β, parseformula("p")), Ł4) == false
@test alphaval(MVLTLFPTableau, ⊤, →(⊤, parseformula("p")), Ł4) == false

@test alphaval(
    MVLTLFPTableau,
    ⊥,
    →(parseformula("p"), parseformula("p")),
    Ł4
) == true
@test alphaval(
    MVLTLFPTableau,
    α,
    →(parseformula("p"), parseformula("p")),
    Ł4
) == true
@test alphaval(
    MVLTLFPTableau,
    β,
    →(parseformula("p"), parseformula("p")),
    Ł4
) == true
@test alphaval(
    MVLTLFPTableau,
    ⊤,
    →(parseformula("p"), parseformula("p")),
    Ł4
) == true

@test alphaval(
    MVLTLFPTableau,
    ⊥,
    →(parseformula("p"), parseformula("q")),
    Ł4
) == true
@test alphaval(
    MVLTLFPTableau,
    α,
    →(parseformula("p"), parseformula("q")),
    Ł4
) == false
@test alphaval(
    MVLTLFPTableau,
    β,
    →(parseformula("p"), parseformula("q")),
    Ł4
) == false
@test alphaval(
    MVLTLFPTableau,
    ⊤,
    →(parseformula("p"), parseformula("q")),
    Ł4
) == false

@test alphaval(
    MVLTLFPTableau,
    ⊥,
    →(parseformula("q"), parseformula("p")),
    Ł4
) == true
@test alphaval(
    MVLTLFPTableau,
    α,
    →(parseformula("q"), parseformula("p")),
    Ł4
) == false
@test alphaval(
    MVLTLFPTableau,
    β,
    →(parseformula("q"), parseformula("p")),
    Ł4
) == false
@test alphaval(
    MVLTLFPTableau,
    ⊤,
    →(parseformula("q"), parseformula("p")),
    Ł4
) == false
