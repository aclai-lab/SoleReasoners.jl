using SoleLogics: Atom
using SoleLogics.ManyValuedLogics: booleanalgebra

p, q, r = Atom.(["p", "q", "r"])

################################################################################
## Propositional logic axioms ##################################################
################################################################################

using SoleLogics: ∧, ∨, →

# Contrapositive:               (p -> q) <-> (¬q -> ¬p)
@test alphasat(
    MVHSTableau,
    ⊤,
    ∧(
        →(→(p, q), →(→(q, ⊥), →(p, ⊥))),
        →(→(→(q, ⊥), →(p, ⊥)) ,→(p, q))
    ),
    booleanalgebra
) == true

# Implication as Disjunction:   (p -> q) <-> (¬p ∨ q)
@test alphasat(
    MVHSTableau,
    ⊤,
    ∧(
        →(→(p, q), ∨(→(p, ⊥), q)),
        →(∨(→(p, ⊥), q), →(p, q))
    ),
    booleanalgebra
) == true

# Distributivity ∧ over ∨:      p ∧ (q ∨ r) <-> (p ∧ q) ∨ (p ∧ r)
@test alphasat(
    MVHSTableau,
    ⊤,
    ∧(
        →(∧(p, ∨(q, r)), ∨(∧(p, q), ∧(p, r))),
        →(∨(∧(p, q), ∧(p, r)), ∧(p, ∨(q, r)))
    ),
    booleanalgebra
) == true

# De Morgan:                    ¬(p ∧ q) <-> ¬p ∨ ¬q
@test alphasat(
    MVHSTableau,
    ⊤,
    ∧(
        →(→(∧(p, q), ⊥), ∨(→(p, ⊥), →(q, ⊥))),
        →(∨(→(p, ⊥), →(q, ⊥)), →(∧(p, q), ⊥)),
    ),
    booleanalgebra
) == true

# De Morgan:                    ¬(p ∨ q) <-> ¬p ∧ ¬q
@test alphasat(
    MVHSTableau,
    ⊤,
    ∧(
        →(→(∨(p, q), ⊥), ∧(→(p, ⊥), →(q, ⊥))),
        →(∧(→(p, ⊥), →(q, ⊥)), →(∨(p, q), ⊥)),
    ),
    booleanalgebra
) == true

# Idempotence:                  p ∧ p <-> p
@test alphasat(
    MVHSTableau,
    ⊤,
    ∧(
        →(∧(p, p), p),
        →(p, ∧(p, p)),
    ),
    booleanalgebra
) == true

# Identity:                     p ∧ ⊤ <-> p
@test alphasat(
    MVHSTableau,
    ⊤,
    ∧(
        →(∧(p, ⊤), p),
        →(p, ∧(p, ⊤)),
    ),
    booleanalgebra
) == true

# Double Negation:              ¬¬p <-> p
@test alphasat(
    MVHSTableau,
    ⊤,
    ∧(
        →(→(→(p, ⊥), ⊥), p),
        →(p, →(→(p, ⊥), ⊥)),
    ),
    booleanalgebra
) == true

# Modus Ponens:                 p ∧ (p -> q) -> q
@test alphasat(
    MVHSTableau,
    ⊤,
    ∧(
        →(∧(p, →(p, q)), q),
        →(q, ∧(p, →(p, q))),
    ),
    booleanalgebra
) == true

# Modus Tollens:                (p -> q) ∧ ¬q -> ¬p
@test alphasat(
    MVHSTableau,
    ⊤,
    ∧(
        →(∧(→(p, q), →(q, ⊥)), →(p, ⊥)),
        →(→(p, ⊥), ∧(→(p, q), →(q, ⊥))),
    ),
    booleanalgebra
) == true

# Disjunctive Syllogism:        ¬p ∧ (p ∨ q) -> q
@test alphasat(
    MVHSTableau,
    ⊤,
    ∧(
        →(∧(→(p, ⊥), ∨(p, q)), q),
        →(q, ∧(→(p, ⊥), ∨(p, q)))
    ),
    booleanalgebra
) == true

################################################################################
## HS logic axioms #############################################################
################################################################################

using SoleLogics: diamond, box
using SoleLogics: HS_A, HS_L, HS_B, HS_E, HS_D, HS_O
using SoleLogics: HS_Ai, HS_Li, HS_Bi, HS_Ei, HS_Di, HS_Oi

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

################################################################################
## K axiom #####################################################################
################################################################################

# (K_X):    [X](p -> q) -> ([X]p -> [X]q)
for boxX in [
    boxA,
    boxL,
    boxB,
    boxE,
    boxD,
    boxO,
    boxAi,
    boxLi,
    boxBi,
    boxEi,
    boxDi,
    boxOi
]
    @test alphasat(
        MVHSTableau,
        ⊤,
        →(boxX(→(p,q)), →(boxX(p), boxX(q))),
        booleanalgebra
    ) == true
end

################################################################################
## Transitivity ################################################################
################################################################################

# (T_X):        <X><X>p -> <X>p (X in [L, B, E, D, Li, Bi, Ei, Di])
for diamondX in [
    diamondL,
    diamondB,
    diamondE,
    diamondD,
    diamondLi,
    diamondBi,
    diamondEi,
    diamondDi
]
    @test alphasat(
        MVHSTableau,
        ⊤,
        →(diamondX(diamondX(p)), diamondX(p)),
        booleanalgebra
    ) == true
end

################################################################################
## Pseudo-transitivity #########################################################
################################################################################

# (Idem_A):     <A><A><A>p -> <A><A>p
@test alphasat(
    MVHSTableau,
    ⊤,
    →(diamondA(diamondA(diamondA(p))), diamondA(diamondA(p))),
    booleanalgebra
) == true

################################################################################
## Temporality #################################################################
################################################################################

# (Temp_A):     <A>[Ai]p -> p
@test alphasat(
    MVHSTableau,
    ⊤,
    →(diamondA(boxAi(p)), p),
    booleanalgebra
) == true

# (Temp_L):     <L>[Li]p -> p
@test alphasat(
    MVHSTableau,
    ⊤,
    →(diamondL(boxLi(p)), p),
    booleanalgebra
) == true

# (Temp_B):     <B>[Bi]p -> p
@test alphasat(
    MVHSTableau,
    ⊤,
    →(diamondB(boxBi(p)), p),
    booleanalgebra
) == true

# (Temp_E):     <E>[Ei]p -> p
@test alphasat(
    MVHSTableau,
    ⊤,
    →(diamondE(boxEi(p)), p),
    booleanalgebra
) == true

# (Temp_D):     <D>[Di]p -> p
@test alphasat(
    MVHSTableau,
    ⊤,
    →(diamondD(boxDi(p)), p),
    booleanalgebra
) == true

# (Temp_O):     <O>[Oi]p -> p
@test alphasat(
    MVHSTableau,
    ⊤,
    →(diamondO(boxOi(p)), p),
    booleanalgebra
) == true

# (Temp_Ai):    <Ai>[A]p -> p
@test alphasat(
    MVHSTableau,
    ⊤,
    →(diamondAi(boxA(p)), p),
    booleanalgebra
) == true

# (Temp_Li):    <Li>[L]p -> p
@test alphasat(
    MVHSTableau,
    ⊤,
    →(diamondLi(boxL(p)), p),
    booleanalgebra
) == true

# (Temp_Bi):    <Bi>[B]p -> p
@test alphasat(
    MVHSTableau,
    ⊤,
    →(diamondBi(boxB(p)), p),
    booleanalgebra
) == true

# (Temp_Ei):    <Ei>[E]p -> p
@test alphasat(
    MVHSTableau,
    ⊤,
    →(diamondEi(boxE(p)), p),
    booleanalgebra
) == true

# (Temp_Di):    <Di>[D]p -> p
@test alphasat(
    MVHSTableau,
    ⊤,
    →(diamondDi(boxD(p)), p),
    booleanalgebra
) == true

# (Temp_Oi):    <Oi>[O]p -> p
@test alphasat(
    MVHSTableau,
    ⊤,
    →(diamondOi(boxO(p)), p),
    booleanalgebra
) == true

################################################################################
## Inverse of temporality ######################################################
################################################################################

# (Int_A):      p -> [A]<Ai>p
@test alphasat(
    MVHSTableau,
    ⊤,
    →(p, boxA(diamondAi(p))),
    booleanalgebra
) == true

# (Int_B):      p -> [B]<Bi>p
@test alphasat(
    MVHSTableau,
    ⊤,
    →(p, boxB(diamondBi(p))),
    booleanalgebra
) == true

# (Int_E):      p -> [E]<Ei>p
@test alphasat(
    MVHSTableau,
    ⊤,
    →(p, boxE(diamondEi(p))),
    booleanalgebra
) == true

# (Int_D):      p -> [D]<Di>p
@test alphasat(
    MVHSTableau,
    ⊤,
    →(p, boxD(diamondDi(p))),
    booleanalgebra
) == true

# (Int_O):      p -> [O]<Oi>p
@test alphasat(
    MVHSTableau,
    ⊤,
    →(p, boxO(diamondOi(p))),
    booleanalgebra
) == true

# (Int_Ai):     p -> [Ai]<A>p
@test alphasat(
    MVHSTableau,
    ⊤,
    →(p, boxAi(diamondA(p))),
    booleanalgebra
) == true

# (Int_Bi):     p -> [Bi]<B>p
@test alphasat(
    MVHSTableau,
    ⊤,
    →(p, boxBi(diamondB(p))),
    booleanalgebra
) == true

# (Int_Ei):     p -> [Ei]<E>p
@test alphasat(
    MVHSTableau,
    ⊤,
    →(p, boxEi(diamondE(p))),
    booleanalgebra
) == true

# (Int_Di):     p -> [Di]<D>p
@test alphasat(
    MVHSTableau,
    ⊤,
    →(p, boxDi(diamondD(p))),
    booleanalgebra
) == true

# (Int_Oi):     p -> [Oi]<O>p
@test alphasat(
    MVHSTableau,
    ⊤,
    →(p, boxOi(diamondO(p))),
    booleanalgebra
) == true

################################################################################
## Stability ###################################################################
################################################################################

# (Stab1_A):    <A><Ai>p -> [A]<Ai>p
@test alphasat(
    MVHSTableau,
    ⊤,
    →(diamondA(diamondAi(p)), boxA(diamondAi(p))),
    booleanalgebra
) == true

# (Stab2_A):    <Ai><A>p -> [Ai]<A>p
@test alphasat(
    MVHSTableau,
    ⊤,
    →(diamondAi(diamondA(p)), boxAi(diamondA(p))),
    booleanalgebra
) == true

# (Stab1_B):    <B><Bi>p -> [B]<Bi>p
@test alphasat(
    MVHSTableau,
    ⊤,
    →(diamondB(diamondBi(p)), boxB(diamondBi(p))),
    booleanalgebra
) == true

# (Stab2_B):    <Bi><B>p -> [Bi]<B>p
@test alphasat(
    MVHSTableau,
    ⊤,
    →(diamondBi(diamondB(p)), boxBi(diamondB(p))),
    booleanalgebra
) == true

# (Stab1_E):    <E><Ei>p -> [E]<Ei>p
@test alphasat(
    MVHSTableau,
    ⊤,
    →(diamondE(diamondEi(p)), boxE(diamondEi(p))),
    booleanalgebra
) == true

# (Stab2_E):    <Ei><E>p -> [Ei]<E>p
@test alphasat(
    MVHSTableau,
    ⊤,
    →(diamondEi(diamondE(p)), boxEi(diamondE(p))),
    booleanalgebra
) == true

################################################################################
## Commutativity ###############################################################
################################################################################

# (C1):     <Bi><Ei>p <-> <Ei><Bi>p
@test alphasat(
    MVHSTableau,
    ⊤,
    ∧(
        →(diamondBi(diamondEi(p)), diamondEi(diamondBi(p))),
        →(diamondEi(diamondBi(p)), diamondBi(diamondEi(p)))
    ),
    booleanalgebra
) == true

# (C2):     <B><E>p <-> <E><B>p
@test alphasat(
    MVHSTableau,
    ⊤,
    ∧(
        →(diamondB(diamondE(p)), diamondE(diamondB(p))),
        →(diamondE(diamondB(p)), diamondB(diamondE(p)))
    ),
    booleanalgebra
) == true

################################################################################
## Definability ################################################################
################################################################################

# (D1):     <L>p <-> <A><A>p
@test alphasat(
    MVHSTableau,
    ⊤,
    ∧(
        →(diamondL(p), diamondA(diamondA(p))),
        →(diamondA(diamondA(p)), diamondL(p))
    ),
    booleanalgebra
) == true

# (D2):     <Li>p <-> <Ai><Ai>p
@test alphasat(
    MVHSTableau,
    ⊤,
    ∧(
        →(diamondLi(p), diamondAi(diamondAi(p))),
        →(diamondAi(diamondAi(p)), diamondLi(p))
    ),
    booleanalgebra
) == true

# (D3):     <D>p <-> <B><E>p
@test alphasat(
    MVHSTableau,
    ⊤,
    ∧(
        →(diamondD(p), diamondB(diamondE(p))),
        →(diamondB(diamondE(p)), diamondD(p))
    ),
    booleanalgebra
) == true

# (D4):     <Di>p <-> <Bi><Ei>p
@test alphasat(
    MVHSTableau,
    ⊤,
    ∧(
        →(diamondDi(p), diamondBi(diamondEi(p))),
        →(diamondBi(diamondEi(p)), diamondDi(p))
    ),
    booleanalgebra
) == true

# (D5):     <O>p <-> <E><Bi>p
@test alphasat(
    MVHSTableau,
    ⊤,
    ∧(
        →(diamondO(p), diamondE(diamondBi(p))),
        →(diamondE(diamondBi(p)), diamondO(p))
    ),
    booleanalgebra
) == true

# (D6):     <Oi>p <-> <B><Ei>p
@test alphasat(
    MVHSTableau,
    ⊤,
    ∧(
        →(diamondOi(p), diamondB(diamondEi(p))),
        →(diamondB(diamondEi(p)), diamondOi(p))
    ),
    booleanalgebra
) == true

################################################################################
## Duality #####################################################################
################################################################################

# (Dual_X):     ¬[X]p <-> <X>¬p
for X in [
    HS_A,
    HS_L,
    HS_B,
    HS_E,
    HS_D,
    HS_Ai,
    HS_Li,
    HS_Bi,
    HS_Ei,
    HS_Di
]
    @test alphasat(
        MVHSTableau,
        ⊤,
        ∧(
            →(→(box(X)(p), ⊥), diamond(X)(→(p, ⊥))),
            →(diamond(X)(→(p, ⊥)), →(box(X)(p), ⊥))
        ),
        booleanalgebra
    ) == true
end
