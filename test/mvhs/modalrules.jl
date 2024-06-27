using SoleLogics: IA_O, converse # momentary fix
using SoleLogics.ManyValuedLogics: G3, H4, α, β

p, q = Atom.(["p", "q"])

max_timeout = 1 # seconds

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
    verbose=false,
    timeout=max_timeout
) == true

@test mvhsalphasat(
    α,
    ∧(diamondA(p), boxA(→(p, ⊥))),
    FiniteHeytingAlgebra(G3),
    verbose=false,
    timeout=max_timeout
) == false

@test mvhsalphasat(
    ⊤,
    ∧(diamondA(p), boxA(→(p, ⊥))),
    FiniteHeytingAlgebra(G3),
    verbose=false,
    timeout=max_timeout
) == false

###################################################
# Examples from Fuzzy Sets and Systems 456 (2023) #
###################################################

f, b = Atom.(["f", "b"])
@test mvhsalphasat(
    α,
    ∧(f,diamondA(b)),
    FiniteHeytingAlgebra(H4),
    verbose=false,
    timeout=max_timeout
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
        FiniteHeytingAlgebra(H4),
        timeout=max_timeout
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
        ),
        FiniteHeytingAlgebra(H4),
        timeout=max_timeout
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
    ),
    FiniteHeytingAlgebra(H4),
    timeout=max_timeout
) == true
for diamondX in [
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
        ),
        FiniteHeytingAlgebra(H4),
        timeout=max_timeout
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
    ),
    FiniteHeytingAlgebra(H4),
    timeout=max_timeout
) == true
@test mvhsalphaprove(
    ⊤,
    →(
        diamondD(p),
        diamondB(diamondE(p))
    ),
    FiniteHeytingAlgebra(H4),
    timeout=max_timeout
) == true
@test mvhsalphaprove(
    ⊤,
    →(
        diamondD(p),
        diamondE(diamondB(p))
    ),
    FiniteHeytingAlgebra(H4),
    timeout=max_timeout
) == true
@test mvhsalphaprove(
    ⊤,
    →(
        diamondO(p),
        diamondE(diamondBi(p))
    ),
    FiniteHeytingAlgebra(H4),
    timeout=max_timeout
) == true
@test mvhsalphaprove(
    ⊤,
    →(
        diamondA(diamondA(p)),
        diamondL(p)
    ),
    FiniteHeytingAlgebra(H4),
    timeout=max_timeout
) == false
@test mvhsalphaprove(
    ⊤,
    →(
        diamondB(diamondE(p)),
        diamondD(p)
    ),
    FiniteHeytingAlgebra(H4),
    timeout=max_timeout
) == false
@test mvhsalphaprove(
    ⊤,
    →(
        diamondE(diamondB(p)),
        diamondD(p)
    ),
    FiniteHeytingAlgebra(H4),
    timeout=max_timeout
) == false
@test mvhsalphaprove(
    ⊤,
    →(
        diamondE(diamondBi(p)),
        diamondO(p)
    ),
    FiniteHeytingAlgebra(H4),
    timeout=max_timeout
) == false
@test mvhsalphaprove(
    ⊤,
    →(
        diamondL(p),
        diamondBi(boxE(diamondBi(diamondE(p))))
    ),
    FiniteHeytingAlgebra(H4),
    timeout=max_timeout
) == false
@test mvhsalphaprove(
    ⊤,
    →(
        diamondBi(boxE(diamondBi(diamondE(p)))),
        diamondL(p)
    ),
    FiniteHeytingAlgebra(H4),
    timeout=max_timeout
) == false

############################################################################################
# FLew Algebra #############################################################################
############################################################################################

###################################################
# Base cases ######################################
###################################################

@test mvhsalphasat(
    ⊥,
    ∧(diamondA(p), boxA(→(p, ⊥))),
    G3,
    verbose=false,
    timeout=max_timeout
) == true

@test mvhsalphasat(
    α,
    ∧(diamondA(p), boxA(→(p, ⊥))),
    G3,
    verbose=false,
    timeout=max_timeout
) == false

@test mvhsalphasat(
    ⊤,
    ∧(diamondA(p), boxA(→(p, ⊥))),
    G3,
    verbose=false,
    timeout=max_timeout
) == false

###################################################
# Examples from Fuzzy Sets and Systems 456 (2023) #
###################################################

f, b = Atom.(["f", "b"])
@test mvhsalphasat(
    α,
    ∧(f,diamondA(b)),
    H4,
    verbose=false,
    timeout=max_timeout
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
        H4,
        timeout=max_timeout
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
        ),
        H4,
        timeout=max_timeout
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
    ),
    H4,
    timeout=max_timeout
) == true
for diamondX in [
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
        ),
        H4,
        timeout=max_timeout
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
    ),
    H4,
    timeout=max_timeout
) == true
@test mvhsalphaprove(
    ⊤,
    →(
        diamondD(p),
        diamondB(diamondE(p))
    ),
    H4,
    timeout=max_timeout
) == true
@test mvhsalphaprove(
    ⊤,
    →(
        diamondD(p),
        diamondE(diamondB(p))
    ),
    H4,
    timeout=max_timeout
) == true
@test mvhsalphaprove(
    ⊤,
    →(
        diamondO(p),
        diamondE(diamondBi(p))
    ),
    H4,
    timeout=max_timeout
) == true
@test mvhsalphaprove(
    ⊤,
    →(
        diamondA(diamondA(p)),
        diamondL(p)
    ),
    H4,
    timeout=max_timeout
) == false
@test mvhsalphaprove(
    ⊤,
    →(
        diamondB(diamondE(p)),
        diamondD(p)
    ),
    H4,
    timeout=max_timeout
) == false
@test mvhsalphaprove(
    ⊤,
    →(
        diamondE(diamondB(p)),
        diamondD(p)
    ),
    H4,
    timeout=max_timeout
) == false
@test mvhsalphaprove(
    ⊤,
    →(
        diamondE(diamondBi(p)),
        diamondO(p)
    ),
    H4,
    timeout=max_timeout
) == false
@test mvhsalphaprove(
    ⊤,
    →(
        diamondL(p),
        diamondBi(boxE(diamondBi(diamondE(p))))
    ),
    H4,
    timeout=max_timeout
) == false
@test mvhsalphaprove(
    ⊤,
    →(
        diamondBi(boxE(diamondBi(diamondE(p)))),
        diamondL(p)
    ),
    H4,
    timeout=max_timeout
) == false