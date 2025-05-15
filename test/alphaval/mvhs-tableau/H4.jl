################################################################################
#### H4 ########################################################################
################################################################################

using SoleLogics.ManyValuedLogics: H4, getdomain
using SoleLogics.ManyValuedLogics: α, β

################################################################################
## Base cases ##################################################################
################################################################################

for i ∈ getdomain(H4)
    for j ∈ getdomain(H4)
        @test alphaval(
            MVHSTableau,
            i,
            j,
        H4) == alphasat(MVHSTableau, i, j, H4)
        for k ∈ getdomain(H4)
            @test alphaval(
                MVHSTableau,
                i,
                ∨(j,k),
                H4
            ) == alphasat(MVHSTableau, i, ∨(j,k), H4)
            @test alphaval(
                MVHSTableau,
                i,
                ∧(j,k),
                H4
            ) == alphasat(MVHSTableau, i, ∧(j,k), H4)
            @test alphaval(
                MVHSTableau,
                i,
                →(j,k),
                H4
            ) == alphasat(MVHSTableau, i, →(j,k), H4)
        end
    end
end

@test alphaval(MVHSTableau, ⊥, parseformula("p"), H4) == true
@test alphaval(MVHSTableau, α, parseformula("p"), H4) == false
@test alphaval(MVHSTableau, β, parseformula("p"), H4) == false
@test alphaval(MVHSTableau, ⊤, parseformula("p"), H4) == false

################################################################################
## (Strong) disjuction #########################################################
################################################################################

@test alphaval(MVHSTableau, ⊥, ∨(parseformula("p"), ⊥), H4) == true
@test alphaval(MVHSTableau, ⊥, ∨(parseformula("p"), α), H4) == true
@test alphaval(MVHSTableau, ⊥, ∨(parseformula("p"), β), H4) == true
@test alphaval(MVHSTableau, ⊥, ∨(parseformula("p"), ⊤), H4) == true
@test alphaval(MVHSTableau, α, ∨(parseformula("p"), ⊥), H4) == false
@test alphaval(MVHSTableau, α, ∨(parseformula("p"), α), H4) == true
@test alphaval(MVHSTableau, α, ∨(parseformula("p"), β), H4) == false
@test alphaval(MVHSTableau, α, ∨(parseformula("p"), ⊤), H4) == true
@test alphaval(MVHSTableau, β, ∨(parseformula("p"), ⊥), H4) == false
@test alphaval(MVHSTableau, β, ∨(parseformula("p"), α), H4) == false
@test alphaval(MVHSTableau, β, ∨(parseformula("p"), β), H4) == true
@test alphaval(MVHSTableau, β, ∨(parseformula("p"), ⊤), H4) == true
@test alphaval(MVHSTableau, ⊤, ∨(parseformula("p"), ⊥), H4) == false
@test alphaval(MVHSTableau, ⊤, ∨(parseformula("p"), α), H4) == false
@test alphaval(MVHSTableau, ⊤, ∨(parseformula("p"), β), H4) == false
@test alphaval(MVHSTableau, ⊤, ∨(parseformula("p"), ⊤), H4) == true

@test alphaval(MVHSTableau, ⊥, ∨(⊥, parseformula("p")), H4) == true 
@test alphaval(MVHSTableau, ⊥, ∨(α, parseformula("p")), H4) == true 
@test alphaval(MVHSTableau, ⊥, ∨(β, parseformula("p")), H4) == true 
@test alphaval(MVHSTableau, ⊥, ∨(⊤, parseformula("p")), H4) == true 
@test alphaval(MVHSTableau, α, ∨(⊥, parseformula("p")), H4) == false
@test alphaval(MVHSTableau, α, ∨(α, parseformula("p")), H4) == true 
@test alphaval(MVHSTableau, α, ∨(β, parseformula("p")), H4) == false 
@test alphaval(MVHSTableau, α, ∨(⊤, parseformula("p")), H4) == true 
@test alphaval(MVHSTableau, β, ∨(⊥, parseformula("p")), H4) == false 
@test alphaval(MVHSTableau, β, ∨(α, parseformula("p")), H4) == false 
@test alphaval(MVHSTableau, β, ∨(β, parseformula("p")), H4) == true 
@test alphaval(MVHSTableau, β, ∨(⊤, parseformula("p")), H4) == true 
@test alphaval(MVHSTableau, ⊤, ∨(⊥, parseformula("p")), H4) == false 
@test alphaval(MVHSTableau, ⊤, ∨(α, parseformula("p")), H4) == false 
@test alphaval(MVHSTableau, ⊤, ∨(β, parseformula("p")), H4) == false 
@test alphaval(MVHSTableau, ⊤, ∨(⊤, parseformula("p")), H4) == true 

@test alphaval(
    MVHSTableau,
    ⊥,
    ∨(parseformula("p"), parseformula("p")),
    H4
) == true
@test alphaval(
    MVHSTableau,
    α,
    ∨(parseformula("p"), parseformula("p")),
    H4
) == false
@test alphaval(
    MVHSTableau,
    β,
    ∨(parseformula("p"), parseformula("p")),
    H4
) == false
@test alphaval(
    MVHSTableau,
    ⊤,
    ∨(parseformula("p"), parseformula("p")),
    H4
) == false

@test alphaval(
    MVHSTableau,
    ⊥,
    ∨(parseformula("p"), parseformula("q")),
    H4
) == true
@test alphaval(
    MVHSTableau,
    α,
    ∨(parseformula("p"), parseformula("q")),
    H4
) == false
@test alphaval(
    MVHSTableau,
    β,
    ∨(parseformula("p"), parseformula("q")),
    H4
) == false
@test alphaval(
    MVHSTableau,
    ⊤,
    ∨(parseformula("p"), parseformula("q")),
    H4
) == false

@test alphaval(
    MVHSTableau,
    ⊥,
    ∨(parseformula("q"), parseformula("p")),
    H4
) == true
@test alphaval(
    MVHSTableau,
    α,
    ∨(parseformula("q"), parseformula("p")),
    H4
) == false
@test alphaval(
    MVHSTableau,
    β,
    ∨(parseformula("q"), parseformula("p")),
    H4
) == false
@test alphaval(
    MVHSTableau,
    ⊤,
    ∨(parseformula("q"), parseformula("p")),
    H4
) == false

################################################################################
## (Strong) conjunction ########################################################
################################################################################

@test alphaval(MVHSTableau, ⊥, ∧(parseformula("p"), ⊥), H4) == true
@test alphaval(MVHSTableau, ⊥, ∧(parseformula("p"), α), H4) == true
@test alphaval(MVHSTableau, ⊥, ∧(parseformula("p"), β), H4) == true
@test alphaval(MVHSTableau, ⊥, ∧(parseformula("p"), ⊤), H4) == true
@test alphaval(MVHSTableau, α, ∧(parseformula("p"), ⊥), H4) == false
@test alphaval(MVHSTableau, α, ∧(parseformula("p"), α), H4) == false
@test alphaval(MVHSTableau, α, ∧(parseformula("p"), β), H4) == false
@test alphaval(MVHSTableau, α, ∧(parseformula("p"), ⊤), H4) == false
@test alphaval(MVHSTableau, β, ∧(parseformula("p"), ⊥), H4) == false
@test alphaval(MVHSTableau, β, ∧(parseformula("p"), α), H4) == false
@test alphaval(MVHSTableau, β, ∧(parseformula("p"), β), H4) == false
@test alphaval(MVHSTableau, β, ∧(parseformula("p"), ⊤), H4) == false
@test alphaval(MVHSTableau, ⊤, ∧(parseformula("p"), ⊥), H4) == false
@test alphaval(MVHSTableau, ⊤, ∧(parseformula("p"), α), H4) == false
@test alphaval(MVHSTableau, ⊤, ∧(parseformula("p"), β), H4) == false
@test alphaval(MVHSTableau, ⊤, ∧(parseformula("p"), ⊤), H4) == false

@test alphaval(MVHSTableau, ⊥, ∧(⊥, parseformula("p")), H4) == true 
@test alphaval(MVHSTableau, ⊥, ∧(α, parseformula("p")), H4) == true 
@test alphaval(MVHSTableau, ⊥, ∧(β, parseformula("p")), H4) == true 
@test alphaval(MVHSTableau, ⊥, ∧(⊤, parseformula("p")), H4) == true 
@test alphaval(MVHSTableau, α, ∧(⊥, parseformula("p")), H4) == false
@test alphaval(MVHSTableau, α, ∧(α, parseformula("p")), H4) == false 
@test alphaval(MVHSTableau, α, ∧(β, parseformula("p")), H4) == false 
@test alphaval(MVHSTableau, α, ∧(⊤, parseformula("p")), H4) == false 
@test alphaval(MVHSTableau, β, ∧(⊥, parseformula("p")), H4) == false 
@test alphaval(MVHSTableau, β, ∧(α, parseformula("p")), H4) == false 
@test alphaval(MVHSTableau, β, ∧(β, parseformula("p")), H4) == false 
@test alphaval(MVHSTableau, β, ∧(⊤, parseformula("p")), H4) == false 
@test alphaval(MVHSTableau, ⊤, ∧(⊥, parseformula("p")), H4) == false 
@test alphaval(MVHSTableau, ⊤, ∧(α, parseformula("p")), H4) == false 
@test alphaval(MVHSTableau, ⊤, ∧(β, parseformula("p")), H4) == false 
@test alphaval(MVHSTableau, ⊤, ∧(⊤, parseformula("p")), H4) == false 

@test alphaval(
    MVHSTableau,
    ⊥,
    ∧(parseformula("p"), parseformula("p")),
    H4
) == true
@test alphaval(
    MVHSTableau,
    α,
    ∧(parseformula("p"), parseformula("p")),
    H4
) == false
@test alphaval(
    MVHSTableau,
    β,
    ∧(parseformula("p"), parseformula("p")),
    H4
) == false
@test alphaval(
    MVHSTableau,
    ⊤,
    ∧(parseformula("p"), parseformula("p")),
    H4
) == false

@test alphaval(
    MVHSTableau,
    ⊥,
    ∧(parseformula("p"), parseformula("q")),
    H4
) == true
@test alphaval(
    MVHSTableau,
    α,
    ∧(parseformula("p"), parseformula("q")),
    H4
) == false
@test alphaval(
    MVHSTableau,
    β,
    ∧(parseformula("p"), parseformula("q")),
    H4
) == false
@test alphaval(
    MVHSTableau,
    ⊤,
    ∧(parseformula("p"), parseformula("q")),
    H4
) == false

@test alphaval(
    MVHSTableau,
    ⊥,
    ∧(parseformula("q"), parseformula("p")),
    H4
) == true
@test alphaval(
    MVHSTableau,
    α,
    ∧(parseformula("q"), parseformula("p")),
    H4
) == false
@test alphaval(
    MVHSTableau,
    β,
    ∧(parseformula("q"), parseformula("p")),
    H4
) == false
@test alphaval(
    MVHSTableau,
    ⊤,
    ∧(parseformula("q"), parseformula("p")),
    H4
) == false

################################################################################
## Implication #################################################################
################################################################################

@test alphaval(MVHSTableau, ⊥, →(parseformula("p"), ⊥), H4) == true
@test alphaval(MVHSTableau, ⊥, →(parseformula("p"), α), H4) == true
@test alphaval(MVHSTableau, ⊥, →(parseformula("p"), β), H4) == true
@test alphaval(MVHSTableau, ⊥, →(parseformula("p"), ⊤), H4) == true
@test alphaval(MVHSTableau, α, →(parseformula("p"), ⊥), H4) == false
@test alphaval(MVHSTableau, α, →(parseformula("p"), α), H4) == true
@test alphaval(MVHSTableau, α, →(parseformula("p"), β), H4) == false
@test alphaval(MVHSTableau, α, →(parseformula("p"), ⊤), H4) == true
@test alphaval(MVHSTableau, β, →(parseformula("p"), ⊥), H4) == false
@test alphaval(MVHSTableau, β, →(parseformula("p"), α), H4) == false
@test alphaval(MVHSTableau, β, →(parseformula("p"), β), H4) == true
@test alphaval(MVHSTableau, β, →(parseformula("p"), ⊤), H4) == true
@test alphaval(MVHSTableau, ⊤, →(parseformula("p"), ⊥), H4) == false
@test alphaval(MVHSTableau, ⊤, →(parseformula("p"), α), H4) == false
@test alphaval(MVHSTableau, ⊤, →(parseformula("p"), β), H4) == false
@test alphaval(MVHSTableau, ⊤, →(parseformula("p"), ⊤), H4) == true

@test alphaval(MVHSTableau, ⊥, →(⊥, parseformula("p")), H4) == true
@test alphaval(MVHSTableau, ⊥, →(α, parseformula("p")), H4) == true
@test alphaval(MVHSTableau, ⊥, →(β, parseformula("p")), H4) == true
@test alphaval(MVHSTableau, ⊥, →(⊤, parseformula("p")), H4) == true
@test alphaval(MVHSTableau, α, →(⊥, parseformula("p")), H4) == true
@test alphaval(MVHSTableau, α, →(α, parseformula("p")), H4) == false
@test alphaval(MVHSTableau, α, →(β, parseformula("p")), H4) == true
@test alphaval(MVHSTableau, α, →(⊤, parseformula("p")), H4) == false
@test alphaval(MVHSTableau, β, →(⊥, parseformula("p")), H4) == true
@test alphaval(MVHSTableau, β, →(α, parseformula("p")), H4) == true
@test alphaval(MVHSTableau, β, →(β, parseformula("p")), H4) == false
@test alphaval(MVHSTableau, β, →(⊤, parseformula("p")), H4) == false
@test alphaval(MVHSTableau, ⊤, →(⊥, parseformula("p")), H4) == true
@test alphaval(MVHSTableau, ⊤, →(α, parseformula("p")), H4) == false
@test alphaval(MVHSTableau, ⊤, →(β, parseformula("p")), H4) == false
@test alphaval(MVHSTableau, ⊤, →(⊤, parseformula("p")), H4) == false

@test alphaval(
    MVHSTableau,
    ⊥,
    →(parseformula("p"), parseformula("p")),
    H4
) == true
@test alphaval(
    MVHSTableau,
    α,
    →(parseformula("p"), parseformula("p")),
    H4
) == true
@test alphaval(
    MVHSTableau,
    β,
    →(parseformula("p"), parseformula("p")),
    H4
) == true
@test alphaval(
    MVHSTableau,
    ⊤,
    →(parseformula("p"), parseformula("p")),
    H4
) == true

@test alphaval(
    MVHSTableau,
    ⊥,
    →(parseformula("p"), parseformula("q")),
    H4
) == true
@test alphaval(
    MVHSTableau,
    α,
    →(parseformula("p"), parseformula("q")),
    H4
) == false
@test alphaval(
    MVHSTableau,
    β,
    →(parseformula("p"), parseformula("q")),
    H4
) == false
@test alphaval(
    MVHSTableau,
    ⊤,
    →(parseformula("p"), parseformula("q")),
    H4
) == false

@test alphaval(
    MVHSTableau,
    ⊥,
    →(parseformula("q"), parseformula("p")),
    H4
) == true
@test alphaval(
    MVHSTableau,
    α,
    →(parseformula("q"), parseformula("p")),
    H4
) == false
@test alphaval(
    MVHSTableau,
    β,
    →(parseformula("q"), parseformula("p")),
    H4
) == false
@test alphaval(
    MVHSTableau,
    ⊤,
    →(parseformula("q"), parseformula("p")),
    H4
) == false
