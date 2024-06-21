using SoleLogics: IA_O, converse # momentary fix
using SoleLogics.ManyValuedLogics: G3, H4, α, β

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

###################################################
# Base cases ######################################
###################################################

@test mvhsalphasat(
    ⊥,
    ∧(diamondA(p), boxA(→(p, ⊥))),
    FiniteHeytingAlgebra(G3),
    verbose=false
) == true

@test mvhsalphasat(
    α,
    ∧(diamondA(p), boxA(→(p, ⊥))),
    FiniteHeytingAlgebra(G3),
    verbose=false
) == false

@test mvhsalphasat(
    ⊤,
    ∧(diamondA(p), boxA(→(p, ⊥))),
    FiniteHeytingAlgebra(G3),
    verbose=false
) == false

###################################################
# Examples from Fuzzy Sets and Systems 456 (2023) #
###################################################

f, b = Atom.(["f", "b"])
@test mvhsalphasat(
    α,
    ∧(f,diamondA(b)),
    FiniteHeytingAlgebra(H4),
    verbose=false
) == true

###################################################
# Properties ######################################
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
    @test mvhsalphaprove(
        ⊤,
        →(
            boxX(→(p,q)),
            →(boxX(p),boxX(q))
        ),
        FiniteHeytingAlgebra(H4)
    ) == true
end
for (boxX,diamondXi) in [
    (boxA,  boxAi),
    (boxL,  boxLi),
    (boxB,  boxBi),
    (boxE,  boxEi),
    (boxD,  boxDi),
    (boxO,  boxOi),
    (boxAi, boxA),
    (boxLi, boxL),
    (boxBi, boxB),
    (boxEi, boxE),
    (boxDi, boxD),
    (boxOi, boxO),
]
    # TODO: inverse version
    @test mvhsalphaprove(
        ⊤,
        →(
            p,
            boxX(diamondXi(p))
        )
    ) == true
end

###################################################
## Theorem 2 ######################################
###################################################
# TODO: inverse version
@test mvhsalphaprove(
    ⊤,
    →(
        diamondD(diamondD(p)),
        diamondD(p)
    )
) == true
for dimaondX in [
    diamondB,
    diamondL,
    diamondE
]
    # TODO: inverse version
    @test mvhsalphaprove(
        ⊤,
        →(
            diamondX(diamondX(p)),
            diamondX(p)
        )
    ) == false
end

###################################################
## Theorem 3 ######################################
###################################################
@test mvhsalphaprove(
    ⊤,
    →(
        diamondL(p),
        diamondA(diamondA(p))
    )
) == true
@test mvhsalphaprove(
    ⊤,
    →(
        diamondD(p),
        diamondB(diamondE(p))
    )
) == true
@test mvhsalphaprove(
    ⊤,
    →(
        diamondD(p),
        diamondE(diamondB(p))
    )
) == true
@test mvhsalphaprove(
    ⊤,
    →(
        diamondO(p),
        diamondE(diamondBi(p))
    )
) == true
@test mvhsalphaprove(
    ⊤,
    →(
        diamondA(diamondA(p)),
        diamondL(p)
    )
) == false
@test mvhsalphaprove(
    ⊤,
    →(
        diamondB(diamondE(p)),
        diamondD(p)
    )
) == false
@test mvhsalphaprove(
    ⊤,
    →(
        diamondE(diamondB(p)),
        diamondD(p)
    )
) == false
@test mvhsalphaprove(
    ⊤,
    →(
        diamondE(diamondBi(p)),
        diamondO(p)
    )
) == false
@test mvhsalphaprove(
    ⊤,
    →(
        diamondL(p),
        diamondBi(boxE(diamondBi(diamondE(p))))
    )
) == false
@test mvhsalphaprove(
    ⊤,
    →(
        diamondBi(boxE(diamondBi(diamondE(p)))),
        diamondL(p)
    )
) == false
