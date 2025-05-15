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
            MVLTLFPTableau,
            i,
            j,
        H4) == alphasat(MVLTLFPTableau, i, j, H4)
        for k ∈ getdomain(H4)
            @test alphaval(
                MVLTLFPTableau,
                i,
                ∨(j,k),
                H4
            ) == alphasat(MVLTLFPTableau, i, ∨(j,k), H4)
            @test alphaval(
                MVLTLFPTableau,
                i,
                ∧(j,k),
                H4
            ) == alphasat(MVLTLFPTableau, i, ∧(j,k), H4)
            @test alphaval(
                MVLTLFPTableau,
                i,
                →(j,k),
                H4
            ) == alphasat(MVLTLFPTableau, i, →(j,k), H4)
        end
    end
end

@test alphaval(MVLTLFPTableau, ⊥, parseformula("p"), H4) == true
@test alphaval(MVLTLFPTableau, α, parseformula("p"), H4) == false
@test alphaval(MVLTLFPTableau, β, parseformula("p"), H4) == false
@test alphaval(MVLTLFPTableau, ⊤, parseformula("p"), H4) == false

################################################################################
## (Strong) disjuction #########################################################
################################################################################

@test alphaval(MVLTLFPTableau, ⊥, ∨(parseformula("p"), ⊥), H4) == true
@test alphaval(MVLTLFPTableau, ⊥, ∨(parseformula("p"), α), H4) == true
@test alphaval(MVLTLFPTableau, ⊥, ∨(parseformula("p"), β), H4) == true
@test alphaval(MVLTLFPTableau, ⊥, ∨(parseformula("p"), ⊤), H4) == true
@test alphaval(MVLTLFPTableau, α, ∨(parseformula("p"), ⊥), H4) == false
@test alphaval(MVLTLFPTableau, α, ∨(parseformula("p"), α), H4) == true
@test alphaval(MVLTLFPTableau, α, ∨(parseformula("p"), β), H4) == false
@test alphaval(MVLTLFPTableau, α, ∨(parseformula("p"), ⊤), H4) == true
@test alphaval(MVLTLFPTableau, β, ∨(parseformula("p"), ⊥), H4) == false
@test alphaval(MVLTLFPTableau, β, ∨(parseformula("p"), α), H4) == false
@test alphaval(MVLTLFPTableau, β, ∨(parseformula("p"), β), H4) == true
@test alphaval(MVLTLFPTableau, β, ∨(parseformula("p"), ⊤), H4) == true
@test alphaval(MVLTLFPTableau, ⊤, ∨(parseformula("p"), ⊥), H4) == false
@test alphaval(MVLTLFPTableau, ⊤, ∨(parseformula("p"), α), H4) == false
@test alphaval(MVLTLFPTableau, ⊤, ∨(parseformula("p"), β), H4) == false
@test alphaval(MVLTLFPTableau, ⊤, ∨(parseformula("p"), ⊤), H4) == true

@test alphaval(MVLTLFPTableau, ⊥, ∨(⊥, parseformula("p")), H4) == true 
@test alphaval(MVLTLFPTableau, ⊥, ∨(α, parseformula("p")), H4) == true 
@test alphaval(MVLTLFPTableau, ⊥, ∨(β, parseformula("p")), H4) == true 
@test alphaval(MVLTLFPTableau, ⊥, ∨(⊤, parseformula("p")), H4) == true 
@test alphaval(MVLTLFPTableau, α, ∨(⊥, parseformula("p")), H4) == false
@test alphaval(MVLTLFPTableau, α, ∨(α, parseformula("p")), H4) == true 
@test alphaval(MVLTLFPTableau, α, ∨(β, parseformula("p")), H4) == false 
@test alphaval(MVLTLFPTableau, α, ∨(⊤, parseformula("p")), H4) == true 
@test alphaval(MVLTLFPTableau, β, ∨(⊥, parseformula("p")), H4) == false 
@test alphaval(MVLTLFPTableau, β, ∨(α, parseformula("p")), H4) == false 
@test alphaval(MVLTLFPTableau, β, ∨(β, parseformula("p")), H4) == true 
@test alphaval(MVLTLFPTableau, β, ∨(⊤, parseformula("p")), H4) == true 
@test alphaval(MVLTLFPTableau, ⊤, ∨(⊥, parseformula("p")), H4) == false 
@test alphaval(MVLTLFPTableau, ⊤, ∨(α, parseformula("p")), H4) == false 
@test alphaval(MVLTLFPTableau, ⊤, ∨(β, parseformula("p")), H4) == false 
@test alphaval(MVLTLFPTableau, ⊤, ∨(⊤, parseformula("p")), H4) == true 

@test alphaval(
    MVLTLFPTableau,
    ⊥,
    ∨(parseformula("p"), parseformula("p")),
    H4
) == true
@test alphaval(
    MVLTLFPTableau,
    α,
    ∨(parseformula("p"), parseformula("p")),
    H4
) == false
@test alphaval(
    MVLTLFPTableau,
    β,
    ∨(parseformula("p"), parseformula("p")),
    H4
) == false
@test alphaval(
    MVLTLFPTableau,
    ⊤,
    ∨(parseformula("p"), parseformula("p")),
    H4
) == false

@test alphaval(
    MVLTLFPTableau,
    ⊥,
    ∨(parseformula("p"), parseformula("q")),
    H4
) == true
@test alphaval(
    MVLTLFPTableau,
    α,
    ∨(parseformula("p"), parseformula("q")),
    H4
) == false
@test alphaval(
    MVLTLFPTableau,
    β,
    ∨(parseformula("p"), parseformula("q")),
    H4
) == false
@test alphaval(
    MVLTLFPTableau,
    ⊤,
    ∨(parseformula("p"), parseformula("q")),
    H4
) == false

@test alphaval(
    MVLTLFPTableau,
    ⊥,
    ∨(parseformula("q"), parseformula("p")),
    H4
) == true
@test alphaval(
    MVLTLFPTableau,
    α,
    ∨(parseformula("q"), parseformula("p")),
    H4
) == false
@test alphaval(
    MVLTLFPTableau,
    β,
    ∨(parseformula("q"), parseformula("p")),
    H4
) == false
@test alphaval(
    MVLTLFPTableau,
    ⊤,
    ∨(parseformula("q"), parseformula("p")),
    H4
) == false

################################################################################
## (Strong) conjunction ########################################################
################################################################################

@test alphaval(MVLTLFPTableau, ⊥, ∧(parseformula("p"), ⊥), H4) == true
@test alphaval(MVLTLFPTableau, ⊥, ∧(parseformula("p"), α), H4) == true
@test alphaval(MVLTLFPTableau, ⊥, ∧(parseformula("p"), β), H4) == true
@test alphaval(MVLTLFPTableau, ⊥, ∧(parseformula("p"), ⊤), H4) == true
@test alphaval(MVLTLFPTableau, α, ∧(parseformula("p"), ⊥), H4) == false
@test alphaval(MVLTLFPTableau, α, ∧(parseformula("p"), α), H4) == false
@test alphaval(MVLTLFPTableau, α, ∧(parseformula("p"), β), H4) == false
@test alphaval(MVLTLFPTableau, α, ∧(parseformula("p"), ⊤), H4) == false
@test alphaval(MVLTLFPTableau, β, ∧(parseformula("p"), ⊥), H4) == false
@test alphaval(MVLTLFPTableau, β, ∧(parseformula("p"), α), H4) == false
@test alphaval(MVLTLFPTableau, β, ∧(parseformula("p"), β), H4) == false
@test alphaval(MVLTLFPTableau, β, ∧(parseformula("p"), ⊤), H4) == false
@test alphaval(MVLTLFPTableau, ⊤, ∧(parseformula("p"), ⊥), H4) == false
@test alphaval(MVLTLFPTableau, ⊤, ∧(parseformula("p"), α), H4) == false
@test alphaval(MVLTLFPTableau, ⊤, ∧(parseformula("p"), β), H4) == false
@test alphaval(MVLTLFPTableau, ⊤, ∧(parseformula("p"), ⊤), H4) == false

@test alphaval(MVLTLFPTableau, ⊥, ∧(⊥, parseformula("p")), H4) == true 
@test alphaval(MVLTLFPTableau, ⊥, ∧(α, parseformula("p")), H4) == true 
@test alphaval(MVLTLFPTableau, ⊥, ∧(β, parseformula("p")), H4) == true 
@test alphaval(MVLTLFPTableau, ⊥, ∧(⊤, parseformula("p")), H4) == true 
@test alphaval(MVLTLFPTableau, α, ∧(⊥, parseformula("p")), H4) == false
@test alphaval(MVLTLFPTableau, α, ∧(α, parseformula("p")), H4) == false 
@test alphaval(MVLTLFPTableau, α, ∧(β, parseformula("p")), H4) == false 
@test alphaval(MVLTLFPTableau, α, ∧(⊤, parseformula("p")), H4) == false 
@test alphaval(MVLTLFPTableau, β, ∧(⊥, parseformula("p")), H4) == false 
@test alphaval(MVLTLFPTableau, β, ∧(α, parseformula("p")), H4) == false 
@test alphaval(MVLTLFPTableau, β, ∧(β, parseformula("p")), H4) == false 
@test alphaval(MVLTLFPTableau, β, ∧(⊤, parseformula("p")), H4) == false 
@test alphaval(MVLTLFPTableau, ⊤, ∧(⊥, parseformula("p")), H4) == false 
@test alphaval(MVLTLFPTableau, ⊤, ∧(α, parseformula("p")), H4) == false 
@test alphaval(MVLTLFPTableau, ⊤, ∧(β, parseformula("p")), H4) == false 
@test alphaval(MVLTLFPTableau, ⊤, ∧(⊤, parseformula("p")), H4) == false 

@test alphaval(
    MVLTLFPTableau,
    ⊥,
    ∧(parseformula("p"), parseformula("p")),
    H4
) == true
@test alphaval(
    MVLTLFPTableau,
    α,
    ∧(parseformula("p"), parseformula("p")),
    H4
) == false
@test alphaval(
    MVLTLFPTableau,
    β,
    ∧(parseformula("p"), parseformula("p")),
    H4
) == false
@test alphaval(
    MVLTLFPTableau,
    ⊤,
    ∧(parseformula("p"), parseformula("p")),
    H4
) == false

@test alphaval(
    MVLTLFPTableau,
    ⊥,
    ∧(parseformula("p"), parseformula("q")),
    H4
) == true
@test alphaval(
    MVLTLFPTableau,
    α,
    ∧(parseformula("p"), parseformula("q")),
    H4
) == false
@test alphaval(
    MVLTLFPTableau,
    β,
    ∧(parseformula("p"), parseformula("q")),
    H4
) == false
@test alphaval(
    MVLTLFPTableau,
    ⊤,
    ∧(parseformula("p"), parseformula("q")),
    H4
) == false

@test alphaval(
    MVLTLFPTableau,
    ⊥,
    ∧(parseformula("q"), parseformula("p")),
    H4
) == true
@test alphaval(
    MVLTLFPTableau,
    α,
    ∧(parseformula("q"), parseformula("p")),
    H4
) == false
@test alphaval(
    MVLTLFPTableau,
    β,
    ∧(parseformula("q"), parseformula("p")),
    H4
) == false
@test alphaval(
    MVLTLFPTableau,
    ⊤,
    ∧(parseformula("q"), parseformula("p")),
    H4
) == false

################################################################################
## Implication #################################################################
################################################################################

@test alphaval(MVLTLFPTableau, ⊥, →(parseformula("p"), ⊥), H4) == true
@test alphaval(MVLTLFPTableau, ⊥, →(parseformula("p"), α), H4) == true
@test alphaval(MVLTLFPTableau, ⊥, →(parseformula("p"), β), H4) == true
@test alphaval(MVLTLFPTableau, ⊥, →(parseformula("p"), ⊤), H4) == true
@test alphaval(MVLTLFPTableau, α, →(parseformula("p"), ⊥), H4) == false
@test alphaval(MVLTLFPTableau, α, →(parseformula("p"), α), H4) == true
@test alphaval(MVLTLFPTableau, α, →(parseformula("p"), β), H4) == false
@test alphaval(MVLTLFPTableau, α, →(parseformula("p"), ⊤), H4) == true
@test alphaval(MVLTLFPTableau, β, →(parseformula("p"), ⊥), H4) == false
@test alphaval(MVLTLFPTableau, β, →(parseformula("p"), α), H4) == false
@test alphaval(MVLTLFPTableau, β, →(parseformula("p"), β), H4) == true
@test alphaval(MVLTLFPTableau, β, →(parseformula("p"), ⊤), H4) == true
@test alphaval(MVLTLFPTableau, ⊤, →(parseformula("p"), ⊥), H4) == false
@test alphaval(MVLTLFPTableau, ⊤, →(parseformula("p"), α), H4) == false
@test alphaval(MVLTLFPTableau, ⊤, →(parseformula("p"), β), H4) == false
@test alphaval(MVLTLFPTableau, ⊤, →(parseformula("p"), ⊤), H4) == true

@test alphaval(MVLTLFPTableau, ⊥, →(⊥, parseformula("p")), H4) == true
@test alphaval(MVLTLFPTableau, ⊥, →(α, parseformula("p")), H4) == true
@test alphaval(MVLTLFPTableau, ⊥, →(β, parseformula("p")), H4) == true
@test alphaval(MVLTLFPTableau, ⊥, →(⊤, parseformula("p")), H4) == true
@test alphaval(MVLTLFPTableau, α, →(⊥, parseformula("p")), H4) == true
@test alphaval(MVLTLFPTableau, α, →(α, parseformula("p")), H4) == false
@test alphaval(MVLTLFPTableau, α, →(β, parseformula("p")), H4) == true
@test alphaval(MVLTLFPTableau, α, →(⊤, parseformula("p")), H4) == false
@test alphaval(MVLTLFPTableau, β, →(⊥, parseformula("p")), H4) == true
@test alphaval(MVLTLFPTableau, β, →(α, parseformula("p")), H4) == true
@test alphaval(MVLTLFPTableau, β, →(β, parseformula("p")), H4) == false
@test alphaval(MVLTLFPTableau, β, →(⊤, parseformula("p")), H4) == false
@test alphaval(MVLTLFPTableau, ⊤, →(⊥, parseformula("p")), H4) == true
@test alphaval(MVLTLFPTableau, ⊤, →(α, parseformula("p")), H4) == false
@test alphaval(MVLTLFPTableau, ⊤, →(β, parseformula("p")), H4) == false
@test alphaval(MVLTLFPTableau, ⊤, →(⊤, parseformula("p")), H4) == false

@test alphaval(
    MVLTLFPTableau,
    ⊥,
    →(parseformula("p"), parseformula("p")),
    H4
) == true
@test alphaval(
    MVLTLFPTableau,
    α,
    →(parseformula("p"), parseformula("p")),
    H4
) == true
@test alphaval(
    MVLTLFPTableau,
    β,
    →(parseformula("p"), parseformula("p")),
    H4
) == true
@test alphaval(
    MVLTLFPTableau,
    ⊤,
    →(parseformula("p"), parseformula("p")),
    H4
) == true

@test alphaval(
    MVLTLFPTableau,
    ⊥,
    →(parseformula("p"), parseformula("q")),
    H4
) == true
@test alphaval(
    MVLTLFPTableau,
    α,
    →(parseformula("p"), parseformula("q")),
    H4
) == false
@test alphaval(
    MVLTLFPTableau,
    β,
    →(parseformula("p"), parseformula("q")),
    H4
) == false
@test alphaval(
    MVLTLFPTableau,
    ⊤,
    →(parseformula("p"), parseformula("q")),
    H4
) == false

@test alphaval(
    MVLTLFPTableau,
    ⊥,
    →(parseformula("q"), parseformula("p")),
    H4
) == true
@test alphaval(
    MVLTLFPTableau,
    α,
    →(parseformula("q"), parseformula("p")),
    H4
) == false
@test alphaval(
    MVLTLFPTableau,
    β,
    →(parseformula("q"), parseformula("p")),
    H4
) == false
@test alphaval(
    MVLTLFPTableau,
    ⊤,
    →(parseformula("q"), parseformula("p")),
    H4
) == false
