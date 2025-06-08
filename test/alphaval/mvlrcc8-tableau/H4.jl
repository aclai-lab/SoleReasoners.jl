################################################################################
#### H4 ########################################################################
################################################################################

using SoleLogics: LRCC8_Rec_DC, LRCC8_Rec_EC, LRCC8_Rec_PO
using SoleLogics: LRCC8_Rec_TPP, LRCC8_Rec_TPPi, LRCC8_Rec_NTPP, LRCC8_Rec_NTPPi
using SoleLogics.ManyValuedLogics: H4
using SoleLogics.ManyValuedLogics: α, β

p, q = Atom.(["p", "q"])

diamondLRCC8_Rec_DC    = diamond(LRCC8_Rec_DC)
diamondLRCC8_Rec_EC    = diamond(LRCC8_Rec_EC)
diamondLRCC8_Rec_PO    = diamond(LRCC8_Rec_PO)
diamondLRCC8_Rec_TPP   = diamond(LRCC8_Rec_TPP)
diamondLRCC8_Rec_TPPi  = diamond(LRCC8_Rec_TPPi)
diamondLRCC8_Rec_NTPP  = diamond(LRCC8_Rec_NTPP)
diamondLRCC8_Rec_NTPPi = diamond(LRCC8_Rec_NTPPi)

boxLRCC8_Rec_DC    = box(LRCC8_Rec_DC)
boxLRCC8_Rec_EC    = box(LRCC8_Rec_EC)
boxLRCC8_Rec_PO    = box(LRCC8_Rec_PO)
boxLRCC8_Rec_TPP   = box(LRCC8_Rec_TPP)
boxLRCC8_Rec_TPPi  = box(LRCC8_Rec_TPPi)
boxLRCC8_Rec_NTPP  = box(LRCC8_Rec_NTPP)
boxLRCC8_Rec_NTPPi = box(LRCC8_Rec_NTPPi)

timeout = 10

################################################################################
## Base cases ##################################################################
################################################################################

for i ∈ getdomain(H4)
    for j ∈ getdomain(H4)
        @test alphaval(
            MVLRCC8Tableau,
            i,
            j,
        H4) == alphasat(MVLRCC8Tableau, i, j, H4)
        for k ∈ getdomain(H4)
            @test alphaval(
                MVLRCC8Tableau,
                i,
                ∨(j,k),
                H4
            ) == alphasat(MVLRCC8Tableau, i, ∨(j,k), H4)
            @test alphaval(
                MVLRCC8Tableau,
                i,
                ∧(j,k),
                H4
            ) == alphasat(MVLRCC8Tableau, i, ∧(j,k), H4)
            @test alphaval(
                MVLRCC8Tableau,
                i,
                →(j,k),
                H4
            ) == alphasat(MVLRCC8Tableau, i, →(j,k), H4)
        end
    end
end

@test alphaval(MVLRCC8Tableau, ⊥, p, H4) == true
@test alphaval(MVLRCC8Tableau, α, p, H4) == false
@test alphaval(MVLRCC8Tableau, β, p, H4) == false
@test alphaval(MVLRCC8Tableau, ⊤, p, H4) == false

################################################################################
## (Strong) disjuction #########################################################
################################################################################

@test alphaval(MVLRCC8Tableau, ⊥, ∨(p, ⊥), H4) == true
@test alphaval(MVLRCC8Tableau, ⊥, ∨(p, α), H4) == true
@test alphaval(MVLRCC8Tableau, ⊥, ∨(p, β), H4) == true
@test alphaval(MVLRCC8Tableau, ⊥, ∨(p, ⊤), H4) == true
@test alphaval(MVLRCC8Tableau, α, ∨(p, ⊥), H4) == false
@test alphaval(MVLRCC8Tableau, α, ∨(p, α), H4) == true
@test alphaval(MVLRCC8Tableau, α, ∨(p, β), H4) == false
@test alphaval(MVLRCC8Tableau, α, ∨(p, ⊤), H4) == true
@test alphaval(MVLRCC8Tableau, β, ∨(p, ⊥), H4) == false
@test alphaval(MVLRCC8Tableau, β, ∨(p, α), H4) == false
@test alphaval(MVLRCC8Tableau, β, ∨(p, β), H4) == true
@test alphaval(MVLRCC8Tableau, β, ∨(p, ⊤), H4) == true
@test alphaval(MVLRCC8Tableau, ⊤, ∨(p, ⊥), H4) == false
@test alphaval(MVLRCC8Tableau, ⊤, ∨(p, α), H4) == false
@test alphaval(MVLRCC8Tableau, ⊤, ∨(p, β), H4) == false
@test alphaval(MVLRCC8Tableau, ⊤, ∨(p, ⊤), H4) == true

@test alphaval(MVLRCC8Tableau, ⊥, ∨(⊥, p), H4) == true 
@test alphaval(MVLRCC8Tableau, ⊥, ∨(α, p), H4) == true 
@test alphaval(MVLRCC8Tableau, ⊥, ∨(β, p), H4) == true 
@test alphaval(MVLRCC8Tableau, ⊥, ∨(⊤, p), H4) == true 
@test alphaval(MVLRCC8Tableau, α, ∨(⊥, p), H4) == false
@test alphaval(MVLRCC8Tableau, α, ∨(α, p), H4) == true 
@test alphaval(MVLRCC8Tableau, α, ∨(β, p), H4) == false 
@test alphaval(MVLRCC8Tableau, α, ∨(⊤, p), H4) == true 
@test alphaval(MVLRCC8Tableau, β, ∨(⊥, p), H4) == false 
@test alphaval(MVLRCC8Tableau, β, ∨(α, p), H4) == false 
@test alphaval(MVLRCC8Tableau, β, ∨(β, p), H4) == true 
@test alphaval(MVLRCC8Tableau, β, ∨(⊤, p), H4) == true 
@test alphaval(MVLRCC8Tableau, ⊤, ∨(⊥, p), H4) == false 
@test alphaval(MVLRCC8Tableau, ⊤, ∨(α, p), H4) == false 
@test alphaval(MVLRCC8Tableau, ⊤, ∨(β, p), H4) == false 
@test alphaval(MVLRCC8Tableau, ⊤, ∨(⊤, p), H4) == true 

@test alphaval(
    MVLRCC8Tableau,
    ⊥,
    ∨(p, p),
    H4
) == true
@test alphaval(
    MVLRCC8Tableau,
    α,
    ∨(p, p),
    H4
) == false
@test alphaval(
    MVLRCC8Tableau,
    β,
    ∨(p, p),
    H4
) == false
@test alphaval(
    MVLRCC8Tableau,
    ⊤,
    ∨(p, p),
    H4
) == false

@test alphaval(
    MVLRCC8Tableau,
    ⊥,
    ∨(p, q),
    H4
) == true
@test alphaval(
    MVLRCC8Tableau,
    α,
    ∨(p, q),
    H4
) == false
@test alphaval(
    MVLRCC8Tableau,
    β,
    ∨(p, q),
    H4
) == false
@test alphaval(
    MVLRCC8Tableau,
    ⊤,
    ∨(p, q),
    H4
) == false

@test alphaval(
    MVLRCC8Tableau,
    ⊥,
    ∨(q, p),
    H4
) == true
@test alphaval(
    MVLRCC8Tableau,
    α,
    ∨(q, p),
    H4
) == false
@test alphaval(
    MVLRCC8Tableau,
    β,
    ∨(q, p),
    H4
) == false
@test alphaval(
    MVLRCC8Tableau,
    ⊤,
    ∨(q, p),
    H4
) == false

################################################################################
## (Strong) conjunction ########################################################
################################################################################

@test alphaval(MVLRCC8Tableau, ⊥, ∧(p, ⊥), H4) == true
@test alphaval(MVLRCC8Tableau, ⊥, ∧(p, α), H4) == true
@test alphaval(MVLRCC8Tableau, ⊥, ∧(p, β), H4) == true
@test alphaval(MVLRCC8Tableau, ⊥, ∧(p, ⊤), H4) == true
@test alphaval(MVLRCC8Tableau, α, ∧(p, ⊥), H4) == false
@test alphaval(MVLRCC8Tableau, α, ∧(p, α), H4) == false
@test alphaval(MVLRCC8Tableau, α, ∧(p, β), H4) == false
@test alphaval(MVLRCC8Tableau, α, ∧(p, ⊤), H4) == false
@test alphaval(MVLRCC8Tableau, β, ∧(p, ⊥), H4) == false
@test alphaval(MVLRCC8Tableau, β, ∧(p, α), H4) == false
@test alphaval(MVLRCC8Tableau, β, ∧(p, β), H4) == false
@test alphaval(MVLRCC8Tableau, β, ∧(p, ⊤), H4) == false
@test alphaval(MVLRCC8Tableau, ⊤, ∧(p, ⊥), H4) == false
@test alphaval(MVLRCC8Tableau, ⊤, ∧(p, α), H4) == false
@test alphaval(MVLRCC8Tableau, ⊤, ∧(p, β), H4) == false
@test alphaval(MVLRCC8Tableau, ⊤, ∧(p, ⊤), H4) == false

@test alphaval(MVLRCC8Tableau, ⊥, ∧(⊥, p), H4) == true 
@test alphaval(MVLRCC8Tableau, ⊥, ∧(α, p), H4) == true 
@test alphaval(MVLRCC8Tableau, ⊥, ∧(β, p), H4) == true 
@test alphaval(MVLRCC8Tableau, ⊥, ∧(⊤, p), H4) == true 
@test alphaval(MVLRCC8Tableau, α, ∧(⊥, p), H4) == false
@test alphaval(MVLRCC8Tableau, α, ∧(α, p), H4) == false 
@test alphaval(MVLRCC8Tableau, α, ∧(β, p), H4) == false 
@test alphaval(MVLRCC8Tableau, α, ∧(⊤, p), H4) == false 
@test alphaval(MVLRCC8Tableau, β, ∧(⊥, p), H4) == false 
@test alphaval(MVLRCC8Tableau, β, ∧(α, p), H4) == false 
@test alphaval(MVLRCC8Tableau, β, ∧(β, p), H4) == false 
@test alphaval(MVLRCC8Tableau, β, ∧(⊤, p), H4) == false 
@test alphaval(MVLRCC8Tableau, ⊤, ∧(⊥, p), H4) == false 
@test alphaval(MVLRCC8Tableau, ⊤, ∧(α, p), H4) == false 
@test alphaval(MVLRCC8Tableau, ⊤, ∧(β, p), H4) == false 
@test alphaval(MVLRCC8Tableau, ⊤, ∧(⊤, p), H4) == false 

@test alphaval(
    MVLRCC8Tableau,
    ⊥,
    ∧(p, p),
    H4
) == true
@test alphaval(
    MVLRCC8Tableau,
    α,
    ∧(p, p),
    H4
) == false
@test alphaval(
    MVLRCC8Tableau,
    β,
    ∧(p, p),
    H4
) == false
@test alphaval(
    MVLRCC8Tableau,
    ⊤,
    ∧(p, p),
    H4
) == false

@test alphaval(
    MVLRCC8Tableau,
    ⊥,
    ∧(p, q),
    H4
) == true
@test alphaval(
    MVLRCC8Tableau,
    α,
    ∧(p, q),
    H4
) == false
@test alphaval(
    MVLRCC8Tableau,
    β,
    ∧(p, q),
    H4
) == false
@test alphaval(
    MVLRCC8Tableau,
    ⊤,
    ∧(p, q),
    H4
) == false

@test alphaval(
    MVLRCC8Tableau,
    ⊥,
    ∧(q, p),
    H4
) == true
@test alphaval(
    MVLRCC8Tableau,
    α,
    ∧(q, p),
    H4
) == false
@test alphaval(
    MVLRCC8Tableau,
    β,
    ∧(q, p),
    H4
) == false
@test alphaval(
    MVLRCC8Tableau,
    ⊤,
    ∧(q, p),
    H4
) == false

################################################################################
## Implication #################################################################
################################################################################

@test alphaval(MVLRCC8Tableau, ⊥, →(p, ⊥), H4) == true
@test alphaval(MVLRCC8Tableau, ⊥, →(p, α), H4) == true
@test alphaval(MVLRCC8Tableau, ⊥, →(p, β), H4) == true
@test alphaval(MVLRCC8Tableau, ⊥, →(p, ⊤), H4) == true
@test alphaval(MVLRCC8Tableau, α, →(p, ⊥), H4) == false
@test alphaval(MVLRCC8Tableau, α, →(p, α), H4) == true
@test alphaval(MVLRCC8Tableau, α, →(p, β), H4) == false
@test alphaval(MVLRCC8Tableau, α, →(p, ⊤), H4) == true
@test alphaval(MVLRCC8Tableau, β, →(p, ⊥), H4) == false
@test alphaval(MVLRCC8Tableau, β, →(p, α), H4) == false
@test alphaval(MVLRCC8Tableau, β, →(p, β), H4) == true
@test alphaval(MVLRCC8Tableau, β, →(p, ⊤), H4) == true
@test alphaval(MVLRCC8Tableau, ⊤, →(p, ⊥), H4) == false
@test alphaval(MVLRCC8Tableau, ⊤, →(p, α), H4) == false
@test alphaval(MVLRCC8Tableau, ⊤, →(p, β), H4) == false
@test alphaval(MVLRCC8Tableau, ⊤, →(p, ⊤), H4) == true

@test alphaval(MVLRCC8Tableau, ⊥, →(⊥, p), H4) == true
@test alphaval(MVLRCC8Tableau, ⊥, →(α, p), H4) == true
@test alphaval(MVLRCC8Tableau, ⊥, →(β, p), H4) == true
@test alphaval(MVLRCC8Tableau, ⊥, →(⊤, p), H4) == true
@test alphaval(MVLRCC8Tableau, α, →(⊥, p), H4) == true
@test alphaval(MVLRCC8Tableau, α, →(α, p), H4) == false
@test alphaval(MVLRCC8Tableau, α, →(β, p), H4) == true
@test alphaval(MVLRCC8Tableau, α, →(⊤, p), H4) == false
@test alphaval(MVLRCC8Tableau, β, →(⊥, p), H4) == true
@test alphaval(MVLRCC8Tableau, β, →(α, p), H4) == true
@test alphaval(MVLRCC8Tableau, β, →(β, p), H4) == false
@test alphaval(MVLRCC8Tableau, β, →(⊤, p), H4) == false
@test alphaval(MVLRCC8Tableau, ⊤, →(⊥, p), H4) == true
@test alphaval(MVLRCC8Tableau, ⊤, →(α, p), H4) == false
@test alphaval(MVLRCC8Tableau, ⊤, →(β, p), H4) == false
@test alphaval(MVLRCC8Tableau, ⊤, →(⊤, p), H4) == false

@test alphaval(
    MVLRCC8Tableau,
    ⊥,
    →(p, p),
    H4
) == true
@test alphaval(
    MVLRCC8Tableau,
    α,
    →(p, p),
    H4
) == true
@test alphaval(
    MVLRCC8Tableau,
    β,
    →(p, p),
    H4
) == true
@test alphaval(
    MVLRCC8Tableau,
    ⊤,
    →(p, p),
    H4
) == true

@test alphaval(
    MVLRCC8Tableau,
    ⊥,
    →(p, q),
    H4
) == true
@test alphaval(
    MVLRCC8Tableau,
    α,
    →(p, q),
    H4
) == false
@test alphaval(
    MVLRCC8Tableau,
    β,
    →(p, q),
    H4
) == false
@test alphaval(
    MVLRCC8Tableau,
    ⊤,
    →(p, q),
    H4
) == false

@test alphaval(
    MVLRCC8Tableau,
    ⊥,
    →(q, p),
    H4
) == true
@test alphaval(
    MVLRCC8Tableau,
    α,
    →(q, p),
    H4
) == false
@test alphaval(
    MVLRCC8Tableau,
    β,
    →(q, p),
    H4
) == false
@test alphaval(
    MVLRCC8Tableau,
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
    boxLRCC8_Rec_DC,
    boxLRCC8_Rec_EC, 
    boxLRCC8_Rec_PO, 
    boxLRCC8_Rec_TPP,    
    boxLRCC8_Rec_TPPi,   
    boxLRCC8_Rec_NTPP,   
    boxLRCC8_Rec_NTPPi
]
    # k axiom
    # TODO: inverse version
    local result = alphaval(
        MVLRCC8Tableau,
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
    (boxLRCC8_Rec_TPP,   diamondLRCC8_Rec_TPPi),
    (boxLRCC8_Rec_TPPi,  diamondLRCC8_Rec_TPP),
    (boxLRCC8_Rec_NTPP,  diamondLRCC8_Rec_NTPPi),
    (boxLRCC8_Rec_NTPPi, diamondLRCC8_Rec_NTPP),
]
    # TODO: inverse version
    local result = alphaval(
        MVLRCC8Tableau,
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
