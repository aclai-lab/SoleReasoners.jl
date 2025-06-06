################################################################################
#### H4 ########################################################################
################################################################################

using SoleLogics.ManyValuedLogics: H4, getdomain
using SoleLogics.ManyValuedLogics: α, β

p, q = Atom.(["p", "q"])

diamondA = diamond(IA_A)
diamondL = diamond(IA_L)
diamondB = diamond(IA_B)
diamondE = diamond(IA_E)
diamondD = diamond(IA_D)
diamondO = diamond(IA_O)
diamondAi = diamond(IA_Ai)
diamondLi = diamond(IA_Li)
diamondBi = diamond(IA_Bi)
diamondEi = diamond(IA_Ei)
diamondDi = diamond(IA_Di)
diamondOi = diamond(IA_Oi)
boxA = box(IA_A)
boxL = box(IA_L)
boxB = box(IA_B)
boxE = box(IA_E)
boxD = box(IA_D)
boxO = box(IA_O)
boxAi = box(IA_Ai)
boxLi = box(IA_Li)
boxBi = box(IA_Bi)
boxEi = box(IA_Ei)
boxDi = box(IA_Di)
boxOi = box(IA_Oi)

timeout = 30

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

@test alphaval(MVHSTableau, ⊥, p, H4) == true
@test alphaval(MVHSTableau, α, p, H4) == false
@test alphaval(MVHSTableau, β, p, H4) == false
@test alphaval(MVHSTableau, ⊤, p, H4) == false

################################################################################
## (Strong) disjuction #########################################################
################################################################################

@test alphaval(MVHSTableau, ⊥, ∨(p, ⊥), H4) == true
@test alphaval(MVHSTableau, ⊥, ∨(p, α), H4) == true
@test alphaval(MVHSTableau, ⊥, ∨(p, β), H4) == true
@test alphaval(MVHSTableau, ⊥, ∨(p, ⊤), H4) == true
@test alphaval(MVHSTableau, α, ∨(p, ⊥), H4) == false
@test alphaval(MVHSTableau, α, ∨(p, α), H4) == true
@test alphaval(MVHSTableau, α, ∨(p, β), H4) == false
@test alphaval(MVHSTableau, α, ∨(p, ⊤), H4) == true
@test alphaval(MVHSTableau, β, ∨(p, ⊥), H4) == false
@test alphaval(MVHSTableau, β, ∨(p, α), H4) == false
@test alphaval(MVHSTableau, β, ∨(p, β), H4) == true
@test alphaval(MVHSTableau, β, ∨(p, ⊤), H4) == true
@test alphaval(MVHSTableau, ⊤, ∨(p, ⊥), H4) == false
@test alphaval(MVHSTableau, ⊤, ∨(p, α), H4) == false
@test alphaval(MVHSTableau, ⊤, ∨(p, β), H4) == false
@test alphaval(MVHSTableau, ⊤, ∨(p, ⊤), H4) == true

@test alphaval(MVHSTableau, ⊥, ∨(⊥, p), H4) == true 
@test alphaval(MVHSTableau, ⊥, ∨(α, p), H4) == true 
@test alphaval(MVHSTableau, ⊥, ∨(β, p), H4) == true 
@test alphaval(MVHSTableau, ⊥, ∨(⊤, p), H4) == true 
@test alphaval(MVHSTableau, α, ∨(⊥, p), H4) == false
@test alphaval(MVHSTableau, α, ∨(α, p), H4) == true 
@test alphaval(MVHSTableau, α, ∨(β, p), H4) == false 
@test alphaval(MVHSTableau, α, ∨(⊤, p), H4) == true 
@test alphaval(MVHSTableau, β, ∨(⊥, p), H4) == false 
@test alphaval(MVHSTableau, β, ∨(α, p), H4) == false 
@test alphaval(MVHSTableau, β, ∨(β, p), H4) == true 
@test alphaval(MVHSTableau, β, ∨(⊤, p), H4) == true 
@test alphaval(MVHSTableau, ⊤, ∨(⊥, p), H4) == false 
@test alphaval(MVHSTableau, ⊤, ∨(α, p), H4) == false 
@test alphaval(MVHSTableau, ⊤, ∨(β, p), H4) == false 
@test alphaval(MVHSTableau, ⊤, ∨(⊤, p), H4) == true 

@test alphaval(
    MVHSTableau,
    ⊥,
    ∨(p, p),
    H4
) == true
@test alphaval(
    MVHSTableau,
    α,
    ∨(p, p),
    H4
) == false
@test alphaval(
    MVHSTableau,
    β,
    ∨(p, p),
    H4
) == false
@test alphaval(
    MVHSTableau,
    ⊤,
    ∨(p, p),
    H4
) == false

@test alphaval(
    MVHSTableau,
    ⊥,
    ∨(p, q),
    H4
) == true
@test alphaval(
    MVHSTableau,
    α,
    ∨(p, q),
    H4
) == false
@test alphaval(
    MVHSTableau,
    β,
    ∨(p, q),
    H4
) == false
@test alphaval(
    MVHSTableau,
    ⊤,
    ∨(p, q),
    H4
) == false

@test alphaval(
    MVHSTableau,
    ⊥,
    ∨(q, p),
    H4
) == true
@test alphaval(
    MVHSTableau,
    α,
    ∨(q, p),
    H4
) == false
@test alphaval(
    MVHSTableau,
    β,
    ∨(q, p),
    H4
) == false
@test alphaval(
    MVHSTableau,
    ⊤,
    ∨(q, p),
    H4
) == false

################################################################################
## (Strong) conjunction ########################################################
################################################################################

@test alphaval(MVHSTableau, ⊥, ∧(p, ⊥), H4) == true
@test alphaval(MVHSTableau, ⊥, ∧(p, α), H4) == true
@test alphaval(MVHSTableau, ⊥, ∧(p, β), H4) == true
@test alphaval(MVHSTableau, ⊥, ∧(p, ⊤), H4) == true
@test alphaval(MVHSTableau, α, ∧(p, ⊥), H4) == false
@test alphaval(MVHSTableau, α, ∧(p, α), H4) == false
@test alphaval(MVHSTableau, α, ∧(p, β), H4) == false
@test alphaval(MVHSTableau, α, ∧(p, ⊤), H4) == false
@test alphaval(MVHSTableau, β, ∧(p, ⊥), H4) == false
@test alphaval(MVHSTableau, β, ∧(p, α), H4) == false
@test alphaval(MVHSTableau, β, ∧(p, β), H4) == false
@test alphaval(MVHSTableau, β, ∧(p, ⊤), H4) == false
@test alphaval(MVHSTableau, ⊤, ∧(p, ⊥), H4) == false
@test alphaval(MVHSTableau, ⊤, ∧(p, α), H4) == false
@test alphaval(MVHSTableau, ⊤, ∧(p, β), H4) == false
@test alphaval(MVHSTableau, ⊤, ∧(p, ⊤), H4) == false

@test alphaval(MVHSTableau, ⊥, ∧(⊥, p), H4) == true 
@test alphaval(MVHSTableau, ⊥, ∧(α, p), H4) == true 
@test alphaval(MVHSTableau, ⊥, ∧(β, p), H4) == true 
@test alphaval(MVHSTableau, ⊥, ∧(⊤, p), H4) == true 
@test alphaval(MVHSTableau, α, ∧(⊥, p), H4) == false
@test alphaval(MVHSTableau, α, ∧(α, p), H4) == false 
@test alphaval(MVHSTableau, α, ∧(β, p), H4) == false 
@test alphaval(MVHSTableau, α, ∧(⊤, p), H4) == false 
@test alphaval(MVHSTableau, β, ∧(⊥, p), H4) == false 
@test alphaval(MVHSTableau, β, ∧(α, p), H4) == false 
@test alphaval(MVHSTableau, β, ∧(β, p), H4) == false 
@test alphaval(MVHSTableau, β, ∧(⊤, p), H4) == false 
@test alphaval(MVHSTableau, ⊤, ∧(⊥, p), H4) == false 
@test alphaval(MVHSTableau, ⊤, ∧(α, p), H4) == false 
@test alphaval(MVHSTableau, ⊤, ∧(β, p), H4) == false 
@test alphaval(MVHSTableau, ⊤, ∧(⊤, p), H4) == false 

@test alphaval(
    MVHSTableau,
    ⊥,
    ∧(p, p),
    H4
) == true
@test alphaval(
    MVHSTableau,
    α,
    ∧(p, p),
    H4
) == false
@test alphaval(
    MVHSTableau,
    β,
    ∧(p, p),
    H4
) == false
@test alphaval(
    MVHSTableau,
    ⊤,
    ∧(p, p),
    H4
) == false

@test alphaval(
    MVHSTableau,
    ⊥,
    ∧(p, q),
    H4
) == true
@test alphaval(
    MVHSTableau,
    α,
    ∧(p, q),
    H4
) == false
@test alphaval(
    MVHSTableau,
    β,
    ∧(p, q),
    H4
) == false
@test alphaval(
    MVHSTableau,
    ⊤,
    ∧(p, q),
    H4
) == false

@test alphaval(
    MVHSTableau,
    ⊥,
    ∧(q, p),
    H4
) == true
@test alphaval(
    MVHSTableau,
    α,
    ∧(q, p),
    H4
) == false
@test alphaval(
    MVHSTableau,
    β,
    ∧(q, p),
    H4
) == false
@test alphaval(
    MVHSTableau,
    ⊤,
    ∧(q, p),
    H4
) == false

################################################################################
## Implication #################################################################
################################################################################

@test alphaval(MVHSTableau, ⊥, →(p, ⊥), H4) == true
@test alphaval(MVHSTableau, ⊥, →(p, α), H4) == true
@test alphaval(MVHSTableau, ⊥, →(p, β), H4) == true
@test alphaval(MVHSTableau, ⊥, →(p, ⊤), H4) == true
@test alphaval(MVHSTableau, α, →(p, ⊥), H4) == false
@test alphaval(MVHSTableau, α, →(p, α), H4) == true
@test alphaval(MVHSTableau, α, →(p, β), H4) == false
@test alphaval(MVHSTableau, α, →(p, ⊤), H4) == true
@test alphaval(MVHSTableau, β, →(p, ⊥), H4) == false
@test alphaval(MVHSTableau, β, →(p, α), H4) == false
@test alphaval(MVHSTableau, β, →(p, β), H4) == true
@test alphaval(MVHSTableau, β, →(p, ⊤), H4) == true
@test alphaval(MVHSTableau, ⊤, →(p, ⊥), H4) == false
@test alphaval(MVHSTableau, ⊤, →(p, α), H4) == false
@test alphaval(MVHSTableau, ⊤, →(p, β), H4) == false
@test alphaval(MVHSTableau, ⊤, →(p, ⊤), H4) == true

@test alphaval(MVHSTableau, ⊥, →(⊥, p), H4) == true
@test alphaval(MVHSTableau, ⊥, →(α, p), H4) == true
@test alphaval(MVHSTableau, ⊥, →(β, p), H4) == true
@test alphaval(MVHSTableau, ⊥, →(⊤, p), H4) == true
@test alphaval(MVHSTableau, α, →(⊥, p), H4) == true
@test alphaval(MVHSTableau, α, →(α, p), H4) == false
@test alphaval(MVHSTableau, α, →(β, p), H4) == true
@test alphaval(MVHSTableau, α, →(⊤, p), H4) == false
@test alphaval(MVHSTableau, β, →(⊥, p), H4) == true
@test alphaval(MVHSTableau, β, →(α, p), H4) == true
@test alphaval(MVHSTableau, β, →(β, p), H4) == false
@test alphaval(MVHSTableau, β, →(⊤, p), H4) == false
@test alphaval(MVHSTableau, ⊤, →(⊥, p), H4) == true
@test alphaval(MVHSTableau, ⊤, →(α, p), H4) == false
@test alphaval(MVHSTableau, ⊤, →(β, p), H4) == false
@test alphaval(MVHSTableau, ⊤, →(⊤, p), H4) == false

@test alphaval(
    MVHSTableau,
    ⊥,
    →(p, p),
    H4
) == true
@test alphaval(
    MVHSTableau,
    α,
    →(p, p),
    H4
) == true
@test alphaval(
    MVHSTableau,
    β,
    →(p, p),
    H4
) == true
@test alphaval(
    MVHSTableau,
    ⊤,
    →(p, p),
    H4
) == true

@test alphaval(
    MVHSTableau,
    ⊥,
    →(p, q),
    H4
) == true
@test alphaval(
    MVHSTableau,
    α,
    →(p, q),
    H4
) == false
@test alphaval(
    MVHSTableau,
    β,
    →(p, q),
    H4
) == false
@test alphaval(
    MVHSTableau,
    ⊤,
    →(p, q),
    H4
) == false

@test alphaval(
    MVHSTableau,
    ⊥,
    →(q, p),
    H4
) == true
@test alphaval(
    MVHSTableau,
    α,
    →(q, p),
    H4
) == false
@test alphaval(
    MVHSTableau,
    β,
    →(q, p),
    H4
) == false
@test alphaval(
    MVHSTableau,
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
    boxA
    boxL
    boxB
    boxE
    boxD
    boxO
    boxAi
    boxLi
    boxBi
    boxEi
    boxDi
    boxOi
]
    # k axiom
    # TODO: inverse version
    local result = alphaval(
        MVHSTableau,
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
    (boxA,  diamondAi),
    (boxL,  diamondLi),
    (boxB,  diamondBi),
    (boxE,  diamondEi),
    (boxD,  diamondDi),
    (boxO,  diamondOi),
    (boxAi, diamondA),
    (boxLi, diamondL),
    (boxBi, diamondB),
    (boxEi, diamondE),
    (boxDi, diamondD),
    (boxOi, diamondO),
]
    # TODO: inverse version
    local result = alphaval(
        MVHSTableau,
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

###################################################
## Theorem 2 ######################################
###################################################
# TODO: inverse version
result = alphaval(
    MVHSTableau,
        ⊤,
    →(
        diamondD(diamondD(p)),
        diamondD(p)
    ),
    H4,
    timeout=timeout
)
if !isnothing(result)
    @test result == true
end
for diamondX in [
    diamondB,
    diamondL,
    diamondE
]
    # TODO: inverse version
    local result = alphaval(
        MVHSTableau,
        ⊤,
        →(
            diamondX(diamondX(p)),
            diamondX(p)
        ),
        H4,
        timeout=timeout
    )
    if !isnothing(result)
        @test result == false
    end
end

###################################################
## Theorem 3 ######################################
###################################################
result = alphaval(
    MVHSTableau,
        ⊤,
    →(
        diamondL(p),
        diamondA(diamondA(p))
    ),
    H4,
    timeout=timeout
)
if !isnothing(result)
    @test result == true
end
result = alphaval(
    MVHSTableau,
        ⊤,
    →(
        diamondD(p),
        diamondB(diamondE(p))
    ),
    H4,
    timeout=timeout
)
if !isnothing(result)
    @test result == true
end
result = alphaval(
    MVHSTableau,
        ⊤,
    →(
        diamondD(p),
        diamondE(diamondB(p))
    ),
    H4,
    timeout=timeout
)
if !isnothing(result)
    @test result == true
end
result = alphaval(
    MVHSTableau,
        ⊤,
    →(
        diamondO(p),
        diamondE(diamondBi(p))
    ),
    H4,
    timeout=timeout
)
if !isnothing(result)
    @test result == true
end
result = alphaval(
    MVHSTableau,
        ⊤,
    →(
        diamondA(diamondA(p)),
        diamondL(p)
    ),
    H4,
    timeout=timeout
)
if !isnothing(result)
    @test result == false
end
result = alphaval(
    MVHSTableau,
        ⊤,
    →(
        diamondB(diamondE(p)),
        diamondD(p)
    ),
    H4,
    timeout=timeout
)
if !isnothing(result)
    @test result == false
end
result = alphaval(
    MVHSTableau,
        ⊤,
    →(
        diamondE(diamondB(p)),
        diamondD(p)
    ),
    H4,
    timeout=timeout
)
if !isnothing(result)
    @test result == false
end
result = alphaval(
    MVHSTableau,
        ⊤,
    →(
        diamondE(diamondBi(p)),
        diamondO(p)
    ),
    H4,
    timeout=timeout
)
if !isnothing(result)
    @test result == false
end
result = alphaval(
    MVHSTableau,
        ⊤,
    →(
        diamondL(p),
        diamondBi(boxE(diamondBi(diamondE(p))))
    ),
    H4,
    timeout=timeout
)
if !isnothing(result)
    @test result == false
end
result = alphaval(
    MVHSTableau,
        ⊤,
    →(
        diamondBi(boxE(diamondBi(diamondE(p)))),
        diamondL(p)
    ),
    H4,
    timeout=timeout
)
if !isnothing(result)
    @test result == false
end
