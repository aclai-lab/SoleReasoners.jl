using SoleLogics: Atom, ∧, ∨, →, diamond, box
using SoleLogics: HS_A, HS_L, HS_B, HS_E, HS_D, HS_O
using SoleLogics: HS_Ai, HS_Li, HS_Bi, HS_Ei, HS_Di, HS_Oi
using SoleLogics.ManyValuedLogics: booleanalgebra

p, q, r = Atom.(["p", "q", "r"])

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
## Propositional logic axioms ##################################################
################################################################################

println("Propositional logic axioms")
println("Contrapositive:               (p -> q) <-> (¬q -> ¬p)")

# Contrapositive:               (p -> q) <-> (¬q -> ¬p)
result = alphasat(
    MVHSTableau,
    ⊤,
    ∧(
        →(→(p, q), →(→(q, ⊥), →(p, ⊥))),
        →(→(→(q, ⊥), →(p, ⊥)) ,→(p, q))
    ),
    booleanalgebra;
    timeout=timeout
)
if !isnothing(result)
    @test result == true
end

println("Implication as Disjunction:   (p -> q) <-> (¬p ∨ q)")

# Implication as Disjunction:   (p -> q) <-> (¬p ∨ q)
result = alphasat(
    MVHSTableau,
    ⊤,
    ∧(
        →(→(p, q), ∨(→(p, ⊥), q)),
        →(∨(→(p, ⊥), q), →(p, q))
    ),
    booleanalgebra;
    timeout=timeout
)
if !isnothing(result)
    @test result == true
end

println("Distributivity ∧ over ∨:      p ∧ (q ∨ r) <-> (p ∧ q) ∨ (p ∧ r)")

# Distributivity ∧ over ∨:      p ∧ (q ∨ r) <-> (p ∧ q) ∨ (p ∧ r)
result = alphasat(
    MVHSTableau,
    ⊤,
    ∧(
        →(∧(p, ∨(q, r)), ∨(∧(p, q), ∧(p, r))),
        →(∨(∧(p, q), ∧(p, r)), ∧(p, ∨(q, r)))
    ),
    booleanalgebra;
    timeout=timeout
)
if !isnothing(result)
    @test result == true
end

println("De Morgan:                    ¬(p ∧ q) <-> ¬p ∨ ¬q")

# De Morgan:                    ¬(p ∧ q) <-> ¬p ∨ ¬q
result = alphasat(
    MVHSTableau,
    ⊤,
    ∧(
        →(→(∧(p, q), ⊥), ∨(→(p, ⊥), →(q, ⊥))),
        →(∨(→(p, ⊥), →(q, ⊥)), →(∧(p, q), ⊥)),
    ),
    booleanalgebra;
    timeout=timeout
)
if !isnothing(result)
    @test result == true
end

println("De Morgan:                    ¬(p ∨ q) <-> ¬p ∧ ¬q")

# De Morgan:                    ¬(p ∨ q) <-> ¬p ∧ ¬q
result = alphasat(
    MVHSTableau,
    ⊤,
    ∧(
        →(→(∨(p, q), ⊥), ∧(→(p, ⊥), →(q, ⊥))),
        →(∧(→(p, ⊥), →(q, ⊥)), →(∨(p, q), ⊥)),
    ),
    booleanalgebra;
    timeout=timeout
)
if !isnothing(result)
    @test result == true
end

println("Idempotence:                  p ∧ p <-> p")

# Idempotence:                  p ∧ p <-> p
result = alphasat(
    MVHSTableau,
    ⊤,
    ∧(
        →(∧(p, p), p),
        →(p, ∧(p, p)),
    ),
    booleanalgebra;
    timeout=timeout
)
if !isnothing(result)
    @test result == true
end

println("Identity:                     p ∧ ⊤ <-> p")

# Identity:                     p ∧ ⊤ <-> p
result = alphasat(
    MVHSTableau,
    ⊤,
    ∧(
        →(∧(p, ⊤), p),
        →(p, ∧(p, ⊤)),
    ),
    booleanalgebra;
    timeout=timeout
)
if !isnothing(result)
    @test result == true
end

println("Double Negation:              ¬¬p <-> p")

# Double Negation:              ¬¬p <-> p
result = alphasat(
    MVHSTableau,
    ⊤,
    ∧(
        →(→(→(p, ⊥), ⊥), p),
        →(p, →(→(p, ⊥), ⊥)),
    ),
    booleanalgebra;
    timeout=timeout
)
if !isnothing(result)
    @test result == true
end

println("Modus Ponens:                 p ∧ (p -> q) -> q")

# Modus Ponens:                 p ∧ (p -> q) -> q
result = alphasat(
    MVHSTableau,
    ⊤,
    →(∧(p, →(p, q)), q),
    booleanalgebra;
    timeout=timeout
)
if !isnothing(result)
    @test result == true
end

println("Modus Tollens:                (p -> q) ∧ ¬q -> ¬p")

# Modus Tollens:                (p -> q) ∧ ¬q -> ¬p
result = alphasat(
    MVHSTableau,
    ⊤,
    →(∧(→(p, q), →(q, ⊥)), →(p, ⊥)),
    booleanalgebra;
    timeout=timeout
)
if !isnothing(result)
    @test result == true
end

println("Disjunctive Syllogism:        ¬p ∧ (p ∨ q) -> q")

# Disjunctive Syllogism:        ¬p ∧ (p ∨ q) -> q
result = alphasat(
    MVHSTableau,
    ⊤,
    →(∧(→(p, ⊥), ∨(p, q)), q),
    booleanalgebra;
    timeout=timeout
)
if !isnothing(result)
    @test result == true
end

################################################################################
## HS logic axioms #############################################################
################################################################################

println("HS logic axioms")

################################################################################
## K axiom #####################################################################
################################################################################

println("K axiom")
println("(K_X):    [X](p -> q) -> ([X]p -> [X]q)")

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
    println(boxX)
    local result = alphasat(
        MVHSTableau,
        ⊤,
        →(boxX(→(p,q)), →(boxX(p), boxX(q))),
        booleanalgebra;
        timeout=timeout
    )
    if !isnothing(result)
        @test result == true
    end
end

################################################################################
## Transitivity ################################################################
################################################################################

println("Transitivity")
println("(T_X):        <X><X>p -> <X>p (X in [L, B, E, D, Li, Bi, Ei, Di])")

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
    println(diamondX)
    local result = alphasat(
        MVHSTableau,
        ⊤,
        →(diamondX(diamondX(p)), diamondX(p)),
        booleanalgebra;
        timeout=timeout
    )
    if !isnothing(result)
        @test result == true
    end
end

################################################################################
## Pseudo-transitivity #########################################################
################################################################################

println("Pseudo-transitivity")
println("(Idem_A):     <A><A><A>p -> <A><A>p")

# (Idem_A):     <A><A><A>p -> <A><A>p
result = alphasat(
    MVHSTableau,
    ⊤,
    →(diamondA(diamondA(diamondA(p))), diamondA(diamondA(p))),
    booleanalgebra;
    timeout=timeout
)
if !isnothing(result)
    @test result == true
end

################################################################################
## Temporality #################################################################
################################################################################

println("Temporality")
println("(Temp_A):     <A>[Ai]p -> p")

# (Temp_A):     <A>[Ai]p -> p
result = alphasat(
    MVHSTableau,
    ⊤,
    →(diamondA(boxAi(p)), p),
    booleanalgebra;
    timeout=timeout
)
if !isnothing(result)
    @test result == true
end

println("(Temp_L):     <L>[Li]p -> p")

# (Temp_L):     <L>[Li]p -> p
result = alphasat(
    MVHSTableau,
    ⊤,
    →(diamondL(boxLi(p)), p),
    booleanalgebra;
    timeout=timeout
)
if !isnothing(result)
    @test result == true
end

println("(Temp_B):     <B>[Bi]p -> p")

# (Temp_B):     <B>[Bi]p -> p
result = alphasat(
    MVHSTableau,
    ⊤,
    →(diamondB(boxBi(p)), p),
    booleanalgebra;
    timeout=timeout
)
if !isnothing(result)
    @test result == true
end

println("(Temp_E):     <E>[Ei]p -> p")

# (Temp_E):     <E>[Ei]p -> p
result = alphasat(
    MVHSTableau,
    ⊤,
    →(diamondE(boxEi(p)), p),
    booleanalgebra;
    timeout=timeout
)
if !isnothing(result)
    @test result == true
end

println("(Temp_D):     <D>[Di]p -> p")

# (Temp_D):     <D>[Di]p -> p
result = alphasat(
    MVHSTableau,
    ⊤,
    →(diamondD(boxDi(p)), p),
    booleanalgebra;
    timeout=timeout
)
if !isnothing(result)
    @test result == true
end

println("(Temp_O):     <O>[Oi]p -> p")

# (Temp_O):     <O>[Oi]p -> p
result = alphasat(
    MVHSTableau,
    ⊤,
    →(diamondO(boxOi(p)), p),
    booleanalgebra;
    timeout=timeout
)
if !isnothing(result)
    @test result == true
end

println("(Temp_Ai):    <Ai>[A]p -> p")

# (Temp_Ai):    <Ai>[A]p -> p
result = alphasat(
    MVHSTableau,
    ⊤,
    →(diamondAi(boxA(p)), p),
    booleanalgebra;
    timeout=timeout
)
if !isnothing(result)
    @test result == true
end

println("(Temp_Li):    <Li>[L]p -> p")

# (Temp_Li):    <Li>[L]p -> p
result = alphasat(
    MVHSTableau,
    ⊤,
    →(diamondLi(boxL(p)), p),
    booleanalgebra;
    timeout=timeout
)
if !isnothing(result)
    @test result == true
end

println("(Temp_Bi):    <Bi>[B]p -> p")

# (Temp_Bi):    <Bi>[B]p -> p
result = alphasat(
    MVHSTableau,
    ⊤,
    →(diamondBi(boxB(p)), p),
    booleanalgebra;
    timeout=timeout
)
if !isnothing(result)
    @test result == true
end

println("(Temp_Ei):    <Ei>[E]p -> p")

# (Temp_Ei):    <Ei>[E]p -> p
result = alphasat(
    MVHSTableau,
    ⊤,
    →(diamondEi(boxE(p)), p),
    booleanalgebra;
    timeout=timeout
)
if !isnothing(result)
    @test result == true
end

println("(Temp_Di):    <Di>[D]p -> p")

# (Temp_Di):    <Di>[D]p -> p
result = alphasat(
    MVHSTableau,
    ⊤,
    →(diamondDi(boxD(p)), p),
    booleanalgebra;
    timeout=timeout
)
if !isnothing(result)
    @test result == true
end

println("(Temp_Oi):    <Oi>[O]p -> p")

# (Temp_Oi):    <Oi>[O]p -> p
result = alphasat(
    MVHSTableau,
    ⊤,
    →(diamondOi(boxO(p)), p),
    booleanalgebra;
    timeout=timeout
)
if !isnothing(result)
    @test result == true
end

################################################################################
## Inverse of temporality ######################################################
################################################################################

println("Inverse of temporality")
println("(Int_A):      p -> [A]<Ai>p")

# (Int_A):      p -> [A]<Ai>p
result = alphasat(
    MVHSTableau,
    ⊤,
    →(p, boxA(diamondAi(p))),
    booleanalgebra;
    timeout=timeout
)
if !isnothing(result)
    @test result == true
end

println("(Int_B):      p -> [B]<Bi>p")

# (Int_B):      p -> [B]<Bi>p
result = alphasat(
    MVHSTableau,
    ⊤,
    →(p, boxB(diamondBi(p))),
    booleanalgebra;
    timeout=timeout
)
if !isnothing(result)
    @test result == true
end

println("(Int_E):      p -> [E]<Ei>p")

# (Int_E):      p -> [E]<Ei>p
result = alphasat(
    MVHSTableau,
    ⊤,
    →(p, boxE(diamondEi(p))),
    booleanalgebra;
    timeout=timeout
)
if !isnothing(result)
    @test result == true
end

println("(Int_D):      p -> [D]<Di>p")

# (Int_D):      p -> [D]<Di>p
result = alphasat(
    MVHSTableau,
    ⊤,
    →(p, boxD(diamondDi(p))),
    booleanalgebra;
    timeout=timeout
)
if !isnothing(result)
    @test result == true
end

println("(Int_O):      p -> [O]<Oi>p")

# (Int_O):      p -> [O]<Oi>p
result = alphasat(
    MVHSTableau,
    ⊤,
    →(p, boxO(diamondOi(p))),
    booleanalgebra;
    timeout=timeout
)
if !isnothing(result)
    @test result == true
end

println("(Int_Ai):     p -> [Ai]<A>p")

# (Int_Ai):     p -> [Ai]<A>p
result = alphasat(
    MVHSTableau,
    ⊤,
    →(p, boxAi(diamondA(p))),
    booleanalgebra;
    timeout=timeout
)
if !isnothing(result)
    @test result == true
end

println("(Int_Bi):     p -> [Bi]<B>p")

# (Int_Bi):     p -> [Bi]<B>p
result = alphasat(
    MVHSTableau,
    ⊤,
    →(p, boxBi(diamondB(p))),
    booleanalgebra;
    timeout=timeout
)
if !isnothing(result)
    @test result == true
end

println("(Int_Ei):     p -> [Ei]<E>p")

# (Int_Ei):     p -> [Ei]<E>p
result = alphasat(
    MVHSTableau,
    ⊤,
    →(p, boxEi(diamondE(p))),
    booleanalgebra;
    timeout=timeout
)
if !isnothing(result)
    @test result == true
end

println("(Int_Di):     p -> [Di]<D>p")

# (Int_Di):     p -> [Di]<D>p
result = alphasat(
    MVHSTableau,
    ⊤,
    →(p, boxDi(diamondD(p))),
    booleanalgebra;
    timeout=timeout
)
if !isnothing(result)
    @test result == true
end

println("(Int_Oi):     p -> [Oi]<O>p")

# (Int_Oi):     p -> [Oi]<O>p
result = alphasat(
    MVHSTableau,
    ⊤,
    →(p, boxOi(diamondO(p))),
    booleanalgebra;
    timeout=timeout
)
if !isnothing(result)
    @test result == true
end

###############################################################################
# Stability ###################################################################
###############################################################################

println("Stability")
println("(Stab1_A):    <A><Ai>p -> [A]<Ai>p")

# (Stab1_A):    <A><Ai>p -> [A]<Ai>p
result = alphasat(
    MVHSTableau,
    ⊤,
    →(diamondA(diamondAi(p)), boxA(diamondAi(p))),
    booleanalgebra;
    timeout=timeout
)
if !isnothing(result)
    @test result == true
end

println("(Stab2_A):    <Ai><A>p -> [Ai]<A>p")

# (Stab2_A):    <Ai><A>p -> [Ai]<A>p
result = alphasat(
    MVHSTableau,
    ⊤,
    →(diamondAi(diamondA(p)), boxAi(diamondA(p))),
    booleanalgebra;
    timeout=timeout
)
if !isnothing(result)
    @test result == true
end

println("(Stab1_B):    <B><Bi>p -> [B]<Bi>p")

# (Stab1_B):    <B><Bi>p -> [B]<Bi>p
result = alphasat(
    MVHSTableau,
    ⊤,
    →(diamondB(diamondBi(p)), boxB(diamondBi(p))),
    booleanalgebra;
    timeout=timeout
)
if !isnothing(result)
    @test result == true
end

println("(Stab2_B):    <Bi><B>p -> [Bi]<B>p")

# (Stab2_B):    <Bi><B>p -> [Bi]<B>p
result = alphasat(
    MVHSTableau,
    ⊤,
    →(diamondBi(diamondB(p)), boxBi(diamondB(p))),
    booleanalgebra;
    timeout=timeout
)
if !isnothing(result)
    @test result == true
end

println("(Stab1_E):    <E><Ei>p -> [E]<Ei>p")

# (Stab1_E):    <E><Ei>p -> [E]<Ei>p
result = alphasat(
    MVHSTableau,
    ⊤,
    →(diamondE(diamondEi(p)), boxE(diamondEi(p))),
    booleanalgebra;
    timeout=timeout
)
if !isnothing(result)
    @test result == true
end

println("(Stab2_E):    <Ei><E>p -> [Ei]<E>p")

# (Stab2_E):    <Ei><E>p -> [Ei]<E>p
result = alphasat(
    MVHSTableau,
    ⊤,
    →(diamondEi(diamondE(p)), boxEi(diamondE(p))),
    booleanalgebra;
    timeout=timeout
)
if !isnothing(result)
    @test result == true
end

################################################################################
## Commutativity ###############################################################
################################################################################

println("Commutativity")

println("(C1):     <Bi><Ei>p <-> <Ei><Bi>p")

# (C1):     <Bi><Ei>p <-> <Ei><Bi>p
result = alphasat(
    MVHSTableau,
    ⊤,
    ∧(
        →(diamondBi(diamondEi(p)), diamondEi(diamondBi(p))),
        →(diamondEi(diamondBi(p)), diamondBi(diamondEi(p)))
    ),
    booleanalgebra;
    timeout=timeout
)
if !isnothing(result)
    @test result == true
end

println("(C2):     <B><E>p <-> <E><B>p")

# (C2):     <B><E>p <-> <E><B>p
result = alphasat(
    MVHSTableau,
    ⊤,
    ∧(
        →(diamondB(diamondE(p)), diamondE(diamondB(p))),
        →(diamondE(diamondB(p)), diamondB(diamondE(p)))
    ),
    booleanalgebra;
    timeout=timeout
)
if !isnothing(result)
    @test result == true
end

################################################################################
## Definability ################################################################
################################################################################

println("Definability")

println("(D1):     <L>p <-> <A><A>p")

# (D1):     <L>p <-> <A><A>p
result = alphasat(
    MVHSTableau,
    ⊤,
    ∧(
        →(diamondL(p), diamondA(diamondA(p))),
        →(diamondA(diamondA(p)), diamondL(p))
    ),
    booleanalgebra;
    timeout=timeout
)
if !isnothing(result)
    @test result == true
end

println("(D2):     <Li>p <-> <Ai><Ai>p")

# (D2):     <Li>p <-> <Ai><Ai>p
result = alphasat(
    MVHSTableau,
    ⊤,
    ∧(
        →(diamondLi(p), diamondAi(diamondAi(p))),
        →(diamondAi(diamondAi(p)), diamondLi(p))
    ),
    booleanalgebra;
    timeout=timeout
)
if !isnothing(result)
    @test result == true
end

println("(D3):     <D>p <-> <B><E>p")

# (D3):     <D>p <-> <B><E>p
result = alphasat(
    MVHSTableau,
    ⊤,
    ∧(
        →(diamondD(p), diamondB(diamondE(p))),
        →(diamondB(diamondE(p)), diamondD(p))
    ),
    booleanalgebra;
    timeout=timeout
)
if !isnothing(result)
    @test result == true
end

println("(D4):     <Di>p <-> <Bi><Ei>p")

# (D4):     <Di>p <-> <Bi><Ei>p
result = alphasat(
    MVHSTableau,
    ⊤,
    ∧(
        →(diamondDi(p), diamondBi(diamondEi(p))),
        →(diamondBi(diamondEi(p)), diamondDi(p))
    ),
    booleanalgebra;
    timeout=timeout
)
if !isnothing(result)
    @test result == true
end

println("(D5):     <O>p <-> <E><Bi>p")

# (D5):     <O>p <-> <E><Bi>p
result = alphasat(
    MVHSTableau,
    ⊤,
    ∧(
        →(diamondO(p), diamondE(diamondBi(p))),
        →(diamondE(diamondBi(p)), diamondO(p))
    ),
    booleanalgebra;
    timeout=timeout
)
if !isnothing(result)
    @test result == true
end

println("(D6):     <Oi>p <-> <B><Ei>p")

# (D6):     <Oi>p <-> <B><Ei>p
result = alphasat(
    MVHSTableau,
    ⊤,
    ∧(
        →(diamondOi(p), diamondB(diamondEi(p))),
        →(diamondB(diamondEi(p)), diamondOi(p))
    ),
    booleanalgebra;
    timeout=timeout
)
if !isnothing(result)
    @test result == true
end

################################################################################
## Duality #####################################################################
################################################################################

println("Duality")

println("(Dual_X):     ¬[X]p <-> <X>¬p")

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
    println(X)
    local result = alphasat(
        MVHSTableau,
        ⊤,
        ∧(
            →(→(box(X)(p), ⊥), diamond(X)(→(p, ⊥))),
            →(diamond(X)(→(p, ⊥)), →(box(X)(p), ⊥))
        ),
        booleanalgebra;
        timeout=timeout
    )
    if !isnothing(result)
        @test result == true
    end
end
