################################################################################
#### H4 ########################################################################
################################################################################

using SoleLogics: CL_N, CL_S, CL_E, CL_W
using SoleLogics.ManyValuedLogics: H4
using SoleLogics.ManyValuedLogics: α, β

p, q = Atom.(["p", "q"])

diamondCL_N = diamond(CL_N)
diamondCL_S = diamond(CL_S)
diamondCL_E = diamond(CL_E)
diamondCL_W = diamond(CL_W)

boxCL_N = box(CL_N)
boxCL_S = box(CL_S)
boxCL_E = box(CL_E)
boxCL_W = box(CL_W)

timeout = 10

################################################################################
## Base cases ##################################################################
################################################################################

for i ∈ getdomain(H4)
    for j ∈ getdomain(H4)
        @test alphaval(
            MVCLTableau,
            i,
            j,
        H4) == alphasat(MVCLTableau, i, j, H4)
        for k ∈ getdomain(H4)
            @test alphaval(
                MVCLTableau,
                i,
                ∨(j,k),
                H4
            ) == alphasat(MVCLTableau, i, ∨(j,k), H4)
            @test alphaval(
                MVCLTableau,
                i,
                ∧(j,k),
                H4
            ) == alphasat(MVCLTableau, i, ∧(j,k), H4)
            @test alphaval(
                MVCLTableau,
                i,
                →(j,k),
                H4
            ) == alphasat(MVCLTableau, i, →(j,k), H4)
        end
    end
end

@test alphaval(MVCLTableau, ⊥, p, H4) == true
@test alphaval(MVCLTableau, α, p, H4) == false
@test alphaval(MVCLTableau, β, p, H4) == false
@test alphaval(MVCLTableau, ⊤, p, H4) == false

################################################################################
## (Strong) disjuction #########################################################
################################################################################

@test alphaval(MVCLTableau, ⊥, ∨(p, ⊥), H4) == true
@test alphaval(MVCLTableau, ⊥, ∨(p, α), H4) == true
@test alphaval(MVCLTableau, ⊥, ∨(p, β), H4) == true
@test alphaval(MVCLTableau, ⊥, ∨(p, ⊤), H4) == true
@test alphaval(MVCLTableau, α, ∨(p, ⊥), H4) == false
@test alphaval(MVCLTableau, α, ∨(p, α), H4) == true
@test alphaval(MVCLTableau, α, ∨(p, β), H4) == false
@test alphaval(MVCLTableau, α, ∨(p, ⊤), H4) == true
@test alphaval(MVCLTableau, β, ∨(p, ⊥), H4) == false
@test alphaval(MVCLTableau, β, ∨(p, α), H4) == false
@test alphaval(MVCLTableau, β, ∨(p, β), H4) == true
@test alphaval(MVCLTableau, β, ∨(p, ⊤), H4) == true
@test alphaval(MVCLTableau, ⊤, ∨(p, ⊥), H4) == false
@test alphaval(MVCLTableau, ⊤, ∨(p, α), H4) == false
@test alphaval(MVCLTableau, ⊤, ∨(p, β), H4) == false
@test alphaval(MVCLTableau, ⊤, ∨(p, ⊤), H4) == true

@test alphaval(MVCLTableau, ⊥, ∨(⊥, p), H4) == true 
@test alphaval(MVCLTableau, ⊥, ∨(α, p), H4) == true 
@test alphaval(MVCLTableau, ⊥, ∨(β, p), H4) == true 
@test alphaval(MVCLTableau, ⊥, ∨(⊤, p), H4) == true 
@test alphaval(MVCLTableau, α, ∨(⊥, p), H4) == false
@test alphaval(MVCLTableau, α, ∨(α, p), H4) == true 
@test alphaval(MVCLTableau, α, ∨(β, p), H4) == false 
@test alphaval(MVCLTableau, α, ∨(⊤, p), H4) == true 
@test alphaval(MVCLTableau, β, ∨(⊥, p), H4) == false 
@test alphaval(MVCLTableau, β, ∨(α, p), H4) == false 
@test alphaval(MVCLTableau, β, ∨(β, p), H4) == true 
@test alphaval(MVCLTableau, β, ∨(⊤, p), H4) == true 
@test alphaval(MVCLTableau, ⊤, ∨(⊥, p), H4) == false 
@test alphaval(MVCLTableau, ⊤, ∨(α, p), H4) == false 
@test alphaval(MVCLTableau, ⊤, ∨(β, p), H4) == false 
@test alphaval(MVCLTableau, ⊤, ∨(⊤, p), H4) == true 

@test alphaval(
    MVCLTableau,
    ⊥,
    ∨(p, p),
    H4
) == true
@test alphaval(
    MVCLTableau,
    α,
    ∨(p, p),
    H4
) == false
@test alphaval(
    MVCLTableau,
    β,
    ∨(p, p),
    H4
) == false
@test alphaval(
    MVCLTableau,
    ⊤,
    ∨(p, p),
    H4
) == false

@test alphaval(
    MVCLTableau,
    ⊥,
    ∨(p, q),
    H4
) == true
@test alphaval(
    MVCLTableau,
    α,
    ∨(p, q),
    H4
) == false
@test alphaval(
    MVCLTableau,
    β,
    ∨(p, q),
    H4
) == false
@test alphaval(
    MVCLTableau,
    ⊤,
    ∨(p, q),
    H4
) == false

@test alphaval(
    MVCLTableau,
    ⊥,
    ∨(q, p),
    H4
) == true
@test alphaval(
    MVCLTableau,
    α,
    ∨(q, p),
    H4
) == false
@test alphaval(
    MVCLTableau,
    β,
    ∨(q, p),
    H4
) == false
@test alphaval(
    MVCLTableau,
    ⊤,
    ∨(q, p),
    H4
) == false

################################################################################
## (Strong) conjunction ########################################################
################################################################################

@test alphaval(MVCLTableau, ⊥, ∧(p, ⊥), H4) == true
@test alphaval(MVCLTableau, ⊥, ∧(p, α), H4) == true
@test alphaval(MVCLTableau, ⊥, ∧(p, β), H4) == true
@test alphaval(MVCLTableau, ⊥, ∧(p, ⊤), H4) == true
@test alphaval(MVCLTableau, α, ∧(p, ⊥), H4) == false
@test alphaval(MVCLTableau, α, ∧(p, α), H4) == false
@test alphaval(MVCLTableau, α, ∧(p, β), H4) == false
@test alphaval(MVCLTableau, α, ∧(p, ⊤), H4) == false
@test alphaval(MVCLTableau, β, ∧(p, ⊥), H4) == false
@test alphaval(MVCLTableau, β, ∧(p, α), H4) == false
@test alphaval(MVCLTableau, β, ∧(p, β), H4) == false
@test alphaval(MVCLTableau, β, ∧(p, ⊤), H4) == false
@test alphaval(MVCLTableau, ⊤, ∧(p, ⊥), H4) == false
@test alphaval(MVCLTableau, ⊤, ∧(p, α), H4) == false
@test alphaval(MVCLTableau, ⊤, ∧(p, β), H4) == false
@test alphaval(MVCLTableau, ⊤, ∧(p, ⊤), H4) == false

@test alphaval(MVCLTableau, ⊥, ∧(⊥, p), H4) == true 
@test alphaval(MVCLTableau, ⊥, ∧(α, p), H4) == true 
@test alphaval(MVCLTableau, ⊥, ∧(β, p), H4) == true 
@test alphaval(MVCLTableau, ⊥, ∧(⊤, p), H4) == true 
@test alphaval(MVCLTableau, α, ∧(⊥, p), H4) == false
@test alphaval(MVCLTableau, α, ∧(α, p), H4) == false 
@test alphaval(MVCLTableau, α, ∧(β, p), H4) == false 
@test alphaval(MVCLTableau, α, ∧(⊤, p), H4) == false 
@test alphaval(MVCLTableau, β, ∧(⊥, p), H4) == false 
@test alphaval(MVCLTableau, β, ∧(α, p), H4) == false 
@test alphaval(MVCLTableau, β, ∧(β, p), H4) == false 
@test alphaval(MVCLTableau, β, ∧(⊤, p), H4) == false 
@test alphaval(MVCLTableau, ⊤, ∧(⊥, p), H4) == false 
@test alphaval(MVCLTableau, ⊤, ∧(α, p), H4) == false 
@test alphaval(MVCLTableau, ⊤, ∧(β, p), H4) == false 
@test alphaval(MVCLTableau, ⊤, ∧(⊤, p), H4) == false 

@test alphaval(
    MVCLTableau,
    ⊥,
    ∧(p, p),
    H4
) == true
@test alphaval(
    MVCLTableau,
    α,
    ∧(p, p),
    H4
) == false
@test alphaval(
    MVCLTableau,
    β,
    ∧(p, p),
    H4
) == false
@test alphaval(
    MVCLTableau,
    ⊤,
    ∧(p, p),
    H4
) == false

@test alphaval(
    MVCLTableau,
    ⊥,
    ∧(p, q),
    H4
) == true
@test alphaval(
    MVCLTableau,
    α,
    ∧(p, q),
    H4
) == false
@test alphaval(
    MVCLTableau,
    β,
    ∧(p, q),
    H4
) == false
@test alphaval(
    MVCLTableau,
    ⊤,
    ∧(p, q),
    H4
) == false

@test alphaval(
    MVCLTableau,
    ⊥,
    ∧(q, p),
    H4
) == true
@test alphaval(
    MVCLTableau,
    α,
    ∧(q, p),
    H4
) == false
@test alphaval(
    MVCLTableau,
    β,
    ∧(q, p),
    H4
) == false
@test alphaval(
    MVCLTableau,
    ⊤,
    ∧(q, p),
    H4
) == false

################################################################################
## Implication #################################################################
################################################################################

@test alphaval(MVCLTableau, ⊥, →(p, ⊥), H4) == true
@test alphaval(MVCLTableau, ⊥, →(p, α), H4) == true
@test alphaval(MVCLTableau, ⊥, →(p, β), H4) == true
@test alphaval(MVCLTableau, ⊥, →(p, ⊤), H4) == true
@test alphaval(MVCLTableau, α, →(p, ⊥), H4) == false
@test alphaval(MVCLTableau, α, →(p, α), H4) == true
@test alphaval(MVCLTableau, α, →(p, β), H4) == false
@test alphaval(MVCLTableau, α, →(p, ⊤), H4) == true
@test alphaval(MVCLTableau, β, →(p, ⊥), H4) == false
@test alphaval(MVCLTableau, β, →(p, α), H4) == false
@test alphaval(MVCLTableau, β, →(p, β), H4) == true
@test alphaval(MVCLTableau, β, →(p, ⊤), H4) == true
@test alphaval(MVCLTableau, ⊤, →(p, ⊥), H4) == false
@test alphaval(MVCLTableau, ⊤, →(p, α), H4) == false
@test alphaval(MVCLTableau, ⊤, →(p, β), H4) == false
@test alphaval(MVCLTableau, ⊤, →(p, ⊤), H4) == true

@test alphaval(MVCLTableau, ⊥, →(⊥, p), H4) == true
@test alphaval(MVCLTableau, ⊥, →(α, p), H4) == true
@test alphaval(MVCLTableau, ⊥, →(β, p), H4) == true
@test alphaval(MVCLTableau, ⊥, →(⊤, p), H4) == true
@test alphaval(MVCLTableau, α, →(⊥, p), H4) == true
@test alphaval(MVCLTableau, α, →(α, p), H4) == false
@test alphaval(MVCLTableau, α, →(β, p), H4) == true
@test alphaval(MVCLTableau, α, →(⊤, p), H4) == false
@test alphaval(MVCLTableau, β, →(⊥, p), H4) == true
@test alphaval(MVCLTableau, β, →(α, p), H4) == true
@test alphaval(MVCLTableau, β, →(β, p), H4) == false
@test alphaval(MVCLTableau, β, →(⊤, p), H4) == false
@test alphaval(MVCLTableau, ⊤, →(⊥, p), H4) == true
@test alphaval(MVCLTableau, ⊤, →(α, p), H4) == false
@test alphaval(MVCLTableau, ⊤, →(β, p), H4) == false
@test alphaval(MVCLTableau, ⊤, →(⊤, p), H4) == false

@test alphaval(
    MVCLTableau,
    ⊥,
    →(p, p),
    H4
) == true
@test alphaval(
    MVCLTableau,
    α,
    →(p, p),
    H4
) == true
@test alphaval(
    MVCLTableau,
    β,
    →(p, p),
    H4
) == true
@test alphaval(
    MVCLTableau,
    ⊤,
    →(p, p),
    H4
) == true

@test alphaval(
    MVCLTableau,
    ⊥,
    →(p, q),
    H4
) == true
@test alphaval(
    MVCLTableau,
    α,
    →(p, q),
    H4
) == false
@test alphaval(
    MVCLTableau,
    β,
    →(p, q),
    H4
) == false
@test alphaval(
    MVCLTableau,
    ⊤,
    →(p, q),
    H4
) == false

@test alphaval(
    MVCLTableau,
    ⊥,
    →(q, p),
    H4
) == true
@test alphaval(
    MVCLTableau,
    α,
    →(q, p),
    H4
) == false
@test alphaval(
    MVCLTableau,
    β,
    →(q, p),
    H4
) == false
@test alphaval(
    MVCLTableau,
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
    boxCL_N,
    boxCL_S,
    boxCL_E,
    boxCL_W
]
    # k axiom
    # TODO: inverse version
    local result = alphaval(
        MVCLTableau,
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
    (boxCL_N,  diamondCL_S),
    (boxCL_S,  diamondCL_N),
    (boxCL_E,  diamondCL_W),
    (boxCL_W,  diamondCL_E),
]
    # TODO: inverse version
    local result = alphaval(
        MVCLTableau,
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
