using SoleLogics: IA_O, converse # momentary fix
using SoleLogics.ManyValuedLogics: G3, H4
using SoleLogics.ManyValuedLogics: FiniteIndexFLewAlgebra, FiniteIndexTruth

IG3 = convert(FiniteIndexFLewAlgebra, G3)
IH4 = convert(FiniteIndexFLewAlgebra, H4)

p, q = Atom.(["p", "q"])

max_timeout = 60 # seconds
diamondexpansion = 0.1 # 10%
# diamondexpansion = 1.0  # 100%

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

@test hybridmvhsalphasat(
    FiniteIndexTruth(2),
    ∧(diamondA(p), boxA(→(p, FiniteIndexTruth(2)))),
    IG3,
    verbose=false,
    timeout=max_timeout,
    diamondexpansion=diamondexpansion
) == true

@test hybridmvhsalphasat(
    FiniteIndexTruth(3),
    ∧(diamondA(p), boxA(→(p, FiniteIndexTruth(2)))),
    IG3,
    verbose=false,
    timeout=max_timeout,
    diamondexpansion=diamondexpansion
) == false

@test hybridmvhsalphasat(
    FiniteIndexTruth(1),
    ∧(diamondA(p), boxA(→(p, FiniteIndexTruth(2)))),
    IG3,
    verbose=false,
    timeout=max_timeout,
    diamondexpansion=diamondexpansion
) == false

###################################################
# Examples from Fuzzy Sets and Systems 456 (2023) #
###################################################

f, b = Atom.(["f", "b"])
@test hybridmvhsalphasat(
    FiniteIndexTruth(3),
    ∧(f,diamondA(b)),
    IH4,
    verbose=false,
    timeout=max_timeout,
    diamondexpansion=diamondexpansion
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
    @test hybridmvhsalphaprove(
        FiniteIndexTruth(1),
        →(
            boxX(→(p,q)),
            →(boxX(p),boxX(q))
        ),
        IH4,
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
    @test hybridmvhsalphaprove(
        FiniteIndexTruth(1),
        →(
            p,
            boxX(diamondXi(p))
        ),
        IH4,
        timeout=max_timeout
    ) == true
end

###################################################
## Theorem 2 ######################################
###################################################
# TODO: inverse version
@test hybridmvhsalphaprove(
    FiniteIndexTruth(1),
    →(
        diamondD(diamondD(p)),
        diamondD(p)
    ),
    IH4,
    timeout=max_timeout,
    diamondexpansion=diamondexpansion
) == true
for diamondX in [
    diamondB,
    diamondL,
    diamondE
]
    # TODO: inverse version
    @test hybridmvhsalphaprove(
        FiniteIndexTruth(1),
        →(
            diamondX(diamondX(p)),
            diamondX(p)
        ),
        IH4,
        timeout=max_timeout
    ) == false
end

###################################################
## Theorem 3 ######################################
###################################################
@test hybridmvhsalphaprove(
    FiniteIndexTruth(1),
    →(
        diamondL(p),
        diamondA(diamondA(p))
    ),
    IH4,
    timeout=max_timeout,
    diamondexpansion=diamondexpansion
) == true
@test hybridmvhsalphaprove(
    FiniteIndexTruth(1),
    →(
        diamondD(p),
        diamondB(diamondE(p))
    ),
    IH4,
    timeout=max_timeout,
    diamondexpansion=diamondexpansion
) == true
@test hybridmvhsalphaprove(
    FiniteIndexTruth(1),
    →(
        diamondD(p),
        diamondE(diamondB(p))
    ),
    IH4,
    timeout=max_timeout,
    diamondexpansion=diamondexpansion
) == true
@test hybridmvhsalphaprove(
    FiniteIndexTruth(1),
    →(
        diamondO(p),
        diamondE(diamondBi(p))
    ),
    IH4,
    timeout=max_timeout,
    diamondexpansion=diamondexpansion
) == true
@test hybridmvhsalphaprove(
    FiniteIndexTruth(1),
    →(
        diamondA(diamondA(p)),
        diamondL(p)
    ),
    IH4,
    timeout=max_timeout,
    diamondexpansion=diamondexpansion
) == false
@test hybridmvhsalphaprove(
    FiniteIndexTruth(1),
    →(
        diamondB(diamondE(p)),
        diamondD(p)
    ),
    IH4,
    timeout=max_timeout,
    diamondexpansion=diamondexpansion
) == false
@test hybridmvhsalphaprove(
    FiniteIndexTruth(1),
    →(
        diamondE(diamondB(p)),
        diamondD(p)
    ),
    IH4,
    timeout=max_timeout,
    diamondexpansion=diamondexpansion
) == false
@test hybridmvhsalphaprove(
    FiniteIndexTruth(1),
    →(
        diamondE(diamondBi(p)),
        diamondO(p)
    ),
    IH4,
    timeout=max_timeout,
    diamondexpansion=diamondexpansion
) == false
@test hybridmvhsalphaprove(
    FiniteIndexTruth(1),
    →(
        diamondL(p),
        diamondBi(boxE(diamondBi(diamondE(p))))
    ),
    IH4,
    timeout=max_timeout,
    diamondexpansion=diamondexpansion
) == false
@test hybridmvhsalphaprove(
    FiniteIndexTruth(1),
    →(
        diamondBi(boxE(diamondBi(diamondE(p)))),
        diamondL(p)
    ),
    IH4,
    timeout=max_timeout,
    diamondexpansion=diamondexpansion
) == false