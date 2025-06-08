################################################################################
#### H4 ########################################################################
################################################################################

using SoleLogics: LTLFP_F, LTLFP_P
using SoleLogics.ManyValuedLogics: H4, getdomain
using SoleLogics.ManyValuedLogics: α, β

p, q = Atom.(["p", "q"])

diamondLTLFP_F, diamondLTLFP_P = diamond.([LTLFP_F, LTLFP_P])
boxLTLFP_F, boxLTLFP_P = box.([LTLFP_F, LTLFP_P])

timeout = 10

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

@test alphaval(MVLTLFPTableau, ⊥, p, H4) == true
@test alphaval(MVLTLFPTableau, α, p, H4) == false
@test alphaval(MVLTLFPTableau, β, p, H4) == false
@test alphaval(MVLTLFPTableau, ⊤, p, H4) == false

################################################################################
## (Strong) disjuction #########################################################
################################################################################

@test alphaval(MVLTLFPTableau, ⊥, ∨(p, ⊥), H4) == true
@test alphaval(MVLTLFPTableau, ⊥, ∨(p, α), H4) == true
@test alphaval(MVLTLFPTableau, ⊥, ∨(p, β), H4) == true
@test alphaval(MVLTLFPTableau, ⊥, ∨(p, ⊤), H4) == true
@test alphaval(MVLTLFPTableau, α, ∨(p, ⊥), H4) == false
@test alphaval(MVLTLFPTableau, α, ∨(p, α), H4) == true
@test alphaval(MVLTLFPTableau, α, ∨(p, β), H4) == false
@test alphaval(MVLTLFPTableau, α, ∨(p, ⊤), H4) == true
@test alphaval(MVLTLFPTableau, β, ∨(p, ⊥), H4) == false
@test alphaval(MVLTLFPTableau, β, ∨(p, α), H4) == false
@test alphaval(MVLTLFPTableau, β, ∨(p, β), H4) == true
@test alphaval(MVLTLFPTableau, β, ∨(p, ⊤), H4) == true
@test alphaval(MVLTLFPTableau, ⊤, ∨(p, ⊥), H4) == false
@test alphaval(MVLTLFPTableau, ⊤, ∨(p, α), H4) == false
@test alphaval(MVLTLFPTableau, ⊤, ∨(p, β), H4) == false
@test alphaval(MVLTLFPTableau, ⊤, ∨(p, ⊤), H4) == true

@test alphaval(MVLTLFPTableau, ⊥, ∨(⊥, p), H4) == true 
@test alphaval(MVLTLFPTableau, ⊥, ∨(α, p), H4) == true 
@test alphaval(MVLTLFPTableau, ⊥, ∨(β, p), H4) == true 
@test alphaval(MVLTLFPTableau, ⊥, ∨(⊤, p), H4) == true 
@test alphaval(MVLTLFPTableau, α, ∨(⊥, p), H4) == false
@test alphaval(MVLTLFPTableau, α, ∨(α, p), H4) == true 
@test alphaval(MVLTLFPTableau, α, ∨(β, p), H4) == false 
@test alphaval(MVLTLFPTableau, α, ∨(⊤, p), H4) == true 
@test alphaval(MVLTLFPTableau, β, ∨(⊥, p), H4) == false 
@test alphaval(MVLTLFPTableau, β, ∨(α, p), H4) == false 
@test alphaval(MVLTLFPTableau, β, ∨(β, p), H4) == true 
@test alphaval(MVLTLFPTableau, β, ∨(⊤, p), H4) == true 
@test alphaval(MVLTLFPTableau, ⊤, ∨(⊥, p), H4) == false 
@test alphaval(MVLTLFPTableau, ⊤, ∨(α, p), H4) == false 
@test alphaval(MVLTLFPTableau, ⊤, ∨(β, p), H4) == false 
@test alphaval(MVLTLFPTableau, ⊤, ∨(⊤, p), H4) == true 

@test alphaval(
    MVLTLFPTableau,
    ⊥,
    ∨(p, p),
    H4
) == true
@test alphaval(
    MVLTLFPTableau,
    α,
    ∨(p, p),
    H4
) == false
@test alphaval(
    MVLTLFPTableau,
    β,
    ∨(p, p),
    H4
) == false
@test alphaval(
    MVLTLFPTableau,
    ⊤,
    ∨(p, p),
    H4
) == false

@test alphaval(
    MVLTLFPTableau,
    ⊥,
    ∨(p, q),
    H4
) == true
@test alphaval(
    MVLTLFPTableau,
    α,
    ∨(p, q),
    H4
) == false
@test alphaval(
    MVLTLFPTableau,
    β,
    ∨(p, q),
    H4
) == false
@test alphaval(
    MVLTLFPTableau,
    ⊤,
    ∨(p, q),
    H4
) == false

@test alphaval(
    MVLTLFPTableau,
    ⊥,
    ∨(q, p),
    H4
) == true
@test alphaval(
    MVLTLFPTableau,
    α,
    ∨(q, p),
    H4
) == false
@test alphaval(
    MVLTLFPTableau,
    β,
    ∨(q, p),
    H4
) == false
@test alphaval(
    MVLTLFPTableau,
    ⊤,
    ∨(q, p),
    H4
) == false

################################################################################
## (Strong) conjunction ########################################################
################################################################################

@test alphaval(MVLTLFPTableau, ⊥, ∧(p, ⊥), H4) == true
@test alphaval(MVLTLFPTableau, ⊥, ∧(p, α), H4) == true
@test alphaval(MVLTLFPTableau, ⊥, ∧(p, β), H4) == true
@test alphaval(MVLTLFPTableau, ⊥, ∧(p, ⊤), H4) == true
@test alphaval(MVLTLFPTableau, α, ∧(p, ⊥), H4) == false
@test alphaval(MVLTLFPTableau, α, ∧(p, α), H4) == false
@test alphaval(MVLTLFPTableau, α, ∧(p, β), H4) == false
@test alphaval(MVLTLFPTableau, α, ∧(p, ⊤), H4) == false
@test alphaval(MVLTLFPTableau, β, ∧(p, ⊥), H4) == false
@test alphaval(MVLTLFPTableau, β, ∧(p, α), H4) == false
@test alphaval(MVLTLFPTableau, β, ∧(p, β), H4) == false
@test alphaval(MVLTLFPTableau, β, ∧(p, ⊤), H4) == false
@test alphaval(MVLTLFPTableau, ⊤, ∧(p, ⊥), H4) == false
@test alphaval(MVLTLFPTableau, ⊤, ∧(p, α), H4) == false
@test alphaval(MVLTLFPTableau, ⊤, ∧(p, β), H4) == false
@test alphaval(MVLTLFPTableau, ⊤, ∧(p, ⊤), H4) == false

@test alphaval(MVLTLFPTableau, ⊥, ∧(⊥, p), H4) == true 
@test alphaval(MVLTLFPTableau, ⊥, ∧(α, p), H4) == true 
@test alphaval(MVLTLFPTableau, ⊥, ∧(β, p), H4) == true 
@test alphaval(MVLTLFPTableau, ⊥, ∧(⊤, p), H4) == true 
@test alphaval(MVLTLFPTableau, α, ∧(⊥, p), H4) == false
@test alphaval(MVLTLFPTableau, α, ∧(α, p), H4) == false 
@test alphaval(MVLTLFPTableau, α, ∧(β, p), H4) == false 
@test alphaval(MVLTLFPTableau, α, ∧(⊤, p), H4) == false 
@test alphaval(MVLTLFPTableau, β, ∧(⊥, p), H4) == false 
@test alphaval(MVLTLFPTableau, β, ∧(α, p), H4) == false 
@test alphaval(MVLTLFPTableau, β, ∧(β, p), H4) == false 
@test alphaval(MVLTLFPTableau, β, ∧(⊤, p), H4) == false 
@test alphaval(MVLTLFPTableau, ⊤, ∧(⊥, p), H4) == false 
@test alphaval(MVLTLFPTableau, ⊤, ∧(α, p), H4) == false 
@test alphaval(MVLTLFPTableau, ⊤, ∧(β, p), H4) == false 
@test alphaval(MVLTLFPTableau, ⊤, ∧(⊤, p), H4) == false 

@test alphaval(
    MVLTLFPTableau,
    ⊥,
    ∧(p, p),
    H4
) == true
@test alphaval(
    MVLTLFPTableau,
    α,
    ∧(p, p),
    H4
) == false
@test alphaval(
    MVLTLFPTableau,
    β,
    ∧(p, p),
    H4
) == false
@test alphaval(
    MVLTLFPTableau,
    ⊤,
    ∧(p, p),
    H4
) == false

@test alphaval(
    MVLTLFPTableau,
    ⊥,
    ∧(p, q),
    H4
) == true
@test alphaval(
    MVLTLFPTableau,
    α,
    ∧(p, q),
    H4
) == false
@test alphaval(
    MVLTLFPTableau,
    β,
    ∧(p, q),
    H4
) == false
@test alphaval(
    MVLTLFPTableau,
    ⊤,
    ∧(p, q),
    H4
) == false

@test alphaval(
    MVLTLFPTableau,
    ⊥,
    ∧(q, p),
    H4
) == true
@test alphaval(
    MVLTLFPTableau,
    α,
    ∧(q, p),
    H4
) == false
@test alphaval(
    MVLTLFPTableau,
    β,
    ∧(q, p),
    H4
) == false
@test alphaval(
    MVLTLFPTableau,
    ⊤,
    ∧(q, p),
    H4
) == false

################################################################################
## Implication #################################################################
################################################################################

@test alphaval(MVLTLFPTableau, ⊥, →(p, ⊥), H4) == true
@test alphaval(MVLTLFPTableau, ⊥, →(p, α), H4) == true
@test alphaval(MVLTLFPTableau, ⊥, →(p, β), H4) == true
@test alphaval(MVLTLFPTableau, ⊥, →(p, ⊤), H4) == true
@test alphaval(MVLTLFPTableau, α, →(p, ⊥), H4) == false
@test alphaval(MVLTLFPTableau, α, →(p, α), H4) == true
@test alphaval(MVLTLFPTableau, α, →(p, β), H4) == false
@test alphaval(MVLTLFPTableau, α, →(p, ⊤), H4) == true
@test alphaval(MVLTLFPTableau, β, →(p, ⊥), H4) == false
@test alphaval(MVLTLFPTableau, β, →(p, α), H4) == false
@test alphaval(MVLTLFPTableau, β, →(p, β), H4) == true
@test alphaval(MVLTLFPTableau, β, →(p, ⊤), H4) == true
@test alphaval(MVLTLFPTableau, ⊤, →(p, ⊥), H4) == false
@test alphaval(MVLTLFPTableau, ⊤, →(p, α), H4) == false
@test alphaval(MVLTLFPTableau, ⊤, →(p, β), H4) == false
@test alphaval(MVLTLFPTableau, ⊤, →(p, ⊤), H4) == true

@test alphaval(MVLTLFPTableau, ⊥, →(⊥, p), H4) == true
@test alphaval(MVLTLFPTableau, ⊥, →(α, p), H4) == true
@test alphaval(MVLTLFPTableau, ⊥, →(β, p), H4) == true
@test alphaval(MVLTLFPTableau, ⊥, →(⊤, p), H4) == true
@test alphaval(MVLTLFPTableau, α, →(⊥, p), H4) == true
@test alphaval(MVLTLFPTableau, α, →(α, p), H4) == false
@test alphaval(MVLTLFPTableau, α, →(β, p), H4) == true
@test alphaval(MVLTLFPTableau, α, →(⊤, p), H4) == false
@test alphaval(MVLTLFPTableau, β, →(⊥, p), H4) == true
@test alphaval(MVLTLFPTableau, β, →(α, p), H4) == true
@test alphaval(MVLTLFPTableau, β, →(β, p), H4) == false
@test alphaval(MVLTLFPTableau, β, →(⊤, p), H4) == false
@test alphaval(MVLTLFPTableau, ⊤, →(⊥, p), H4) == true
@test alphaval(MVLTLFPTableau, ⊤, →(α, p), H4) == false
@test alphaval(MVLTLFPTableau, ⊤, →(β, p), H4) == false
@test alphaval(MVLTLFPTableau, ⊤, →(⊤, p), H4) == false

@test alphaval(
    MVLTLFPTableau,
    ⊥,
    →(p, p),
    H4
) == true
@test alphaval(
    MVLTLFPTableau,
    α,
    →(p, p),
    H4
) == true
@test alphaval(
    MVLTLFPTableau,
    β,
    →(p, p),
    H4
) == true
@test alphaval(
    MVLTLFPTableau,
    ⊤,
    →(p, p),
    H4
) == true

@test alphaval(
    MVLTLFPTableau,
    ⊥,
    →(p, q),
    H4
) == true
@test alphaval(
    MVLTLFPTableau,
    α,
    →(p, q),
    H4
) == false
@test alphaval(
    MVLTLFPTableau,
    β,
    →(p, q),
    H4
) == false
@test alphaval(
    MVLTLFPTableau,
    ⊤,
    →(p, q),
    H4
) == false

@test alphaval(
    MVLTLFPTableau,
    ⊥,
    →(q, p),
    H4
) == true
@test alphaval(
    MVLTLFPTableau,
    α,
    →(q, p),
    H4
) == false
@test alphaval(
    MVLTLFPTableau,
    β,
    →(q, p),
    H4
) == false
@test alphaval(
    MVLTLFPTableau,
    ⊤,
    →(q, p),
    H4
) == false

################################################################################
#### Modal cases ###############################################################
################################################################################
#### Examples from Fuzzy Sets and Systems 456 (2023) ###########################
################################################################################

###################################################
## Theorem 1 ######################################
###################################################
for boxX in [
    boxLTLFP_F,
    boxLTLFP_P
]
    # k axiom
    # TODO: inverse version
    local result = alphaval(
        MVLTLFPTableau,
        ⊤,
        →(
            boxX(→(p,q)),
            →(boxX(p),boxX(q))
        ),
        H4,
        timeout=timeout
    )
    if !isnothing(result)
        @test result == true
    end
end
for (boxX,diamondXi) in [
    (boxLTLFP_F,  diamondLTLFP_P),
    (boxLTLFP_P,  diamondLTLFP_F)
]
    # TODO: inverse version
    local result = alphaval(
        MVLTLFPTableau,
        ⊤,
        →(
            p,
            boxX(diamondXi(p))
        ),
        H4,
        timeout=timeout
    )
    if !isnothing(result)
        @test result == true
    end
end
