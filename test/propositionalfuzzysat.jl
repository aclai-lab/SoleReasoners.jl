using SoleReasoners
using Graphs

α = HeytingTruth("α", 3)
β = HeytingTruth("β", 4)

booleanalgebra = HeytingAlgebra(
    [HeytingTruth(⊤), HeytingTruth(⊥)],
    Edge.([(⊥, ⊤)]),
    evaluate=true
)

threevaluedalgebra = HeytingAlgebra(
    [HeytingTruth(⊤), HeytingTruth(⊥), α],
    Edge.([(⊥, α), (α, ⊤)]),
    evaluate=true

    )
diamondalgebra = HeytingAlgebra(
    [HeytingTruth(⊤), HeytingTruth(⊥), α, β],
    Edge.([(⊥, α), (⊥, β), (α, ⊤), (β, ⊤)]),
    evaluate=true
)

@test sat(parseformula("⊥"),   booleanalgebra) == false
@test sat(parseformula("⊤"),   booleanalgebra) == true
@test sat(parseformula("⊥∧⊥"), booleanalgebra) == false
@test sat(parseformula("⊥∧⊤"), booleanalgebra) == false
@test sat(parseformula("⊤∧⊥"), booleanalgebra) == false
@test sat(parseformula("⊤∧⊤"), booleanalgebra) == true
@test sat(parseformula("⊥∨⊥"), booleanalgebra) == false
@test sat(parseformula("⊥∨⊤"), booleanalgebra) == true
@test sat(parseformula("⊤∨⊥"), booleanalgebra) == true
@test sat(parseformula("⊤∨⊤"), booleanalgebra) == true
@test sat(parseformula("⊥→⊥"), booleanalgebra) == true
@test sat(parseformula("⊥→⊤"), booleanalgebra) == true
@test sat(parseformula("⊤→⊥"), booleanalgebra) == false
@test sat(parseformula("⊤→⊤"), booleanalgebra) == true

@test sat(parseformula("⊥"),   threevaluedalgebra) == false
@test sat(parseformula("⊤"),   threevaluedalgebra) == true
@test sat(parseformula("⊥∧⊥"), threevaluedalgebra) == false
@test sat(parseformula("⊥∧⊤"), threevaluedalgebra) == false
@test sat(parseformula("⊤∧⊥"), threevaluedalgebra) == false
@test sat(parseformula("⊤∧⊤"), threevaluedalgebra) == true
@test sat(parseformula("⊥∨⊥"), threevaluedalgebra) == false
@test sat(parseformula("⊥∨⊤"), threevaluedalgebra) == true
@test sat(parseformula("⊤∨⊥"), threevaluedalgebra) == true
@test sat(parseformula("⊤∨⊤"), threevaluedalgebra) == true
@test sat(parseformula("⊥→⊥"), threevaluedalgebra) == true
@test sat(parseformula("⊥→⊤"), threevaluedalgebra) == true
@test sat(parseformula("⊤→⊥"), threevaluedalgebra) == false
@test sat(parseformula("⊤→⊤"), threevaluedalgebra) == true

@test sat(parseformula("⊥"),   diamondalgebra) == false
@test sat(parseformula("⊤"),   diamondalgebra) == true
@test sat(parseformula("⊥∧⊥"), diamondalgebra) == false
@test sat(parseformula("⊥∧⊤"), diamondalgebra) == false
@test sat(parseformula("⊤∧⊥"), diamondalgebra) == false
@test sat(parseformula("⊤∧⊤"), diamondalgebra) == true
@test sat(parseformula("⊥∨⊥"), diamondalgebra) == false
@test sat(parseformula("⊥∨⊤"), diamondalgebra) == true
@test sat(parseformula("⊤∨⊥"), diamondalgebra) == true
@test sat(parseformula("⊤∨⊤"), diamondalgebra) == true
@test sat(parseformula("⊥→⊥"), diamondalgebra) == true
@test sat(parseformula("⊥→⊤"), diamondalgebra) == true
@test sat(parseformula("⊤→⊥"), diamondalgebra) == false
@test sat(parseformula("⊤→⊤"), diamondalgebra) == true

@test sat(parseformula("p"), booleanalgebra) == true
@test sat(parseformula("p→⊥"), booleanalgebra) == true
@test sat(parseformula("p∧p"), booleanalgebra) == true
@test sat(parseformula("p∧(p→⊥)"), booleanalgebra) == false
@test sat(parseformula("(p→⊥)∧p"), booleanalgebra) == false
@test sat(parseformula("(p→⊥)∧(p→⊥)"), booleanalgebra) == true
@test sat(parseformula("p∨p"), booleanalgebra) == true
@test sat(parseformula("p∨(p→⊥)"), booleanalgebra) == true
@test sat(parseformula("(p→⊥)∨p"), booleanalgebra) == true
@test sat(parseformula("(p→⊥)∨(p→⊥)"), booleanalgebra) == true
@test sat(parseformula("p→p"), booleanalgebra) == true
@test sat(parseformula("p→(p→⊥)"), booleanalgebra) == true
@test sat(parseformula("(p→⊥)→p"), booleanalgebra) == true
@test sat(parseformula("(p→⊥)→(p→⊥)"), booleanalgebra) == true

@test sat(parseformula("p"), threevaluedalgebra) == true
@test sat(parseformula("p→⊥"), threevaluedalgebra) == true
@test sat(parseformula("p∧p"), threevaluedalgebra) == true
@test sat(parseformula("p∧(p→⊥)"), threevaluedalgebra) == false
@test sat(parseformula("(p→⊥)∧p"), threevaluedalgebra) == false
@test sat(parseformula("(p→⊥)∧(p→⊥)"), threevaluedalgebra) == true
@test sat(parseformula("p∨p"), threevaluedalgebra) == true
@test sat(parseformula("p∨(p→⊥)"), threevaluedalgebra) == true
@test sat(parseformula("(p→⊥)∨p"), threevaluedalgebra) == true
@test sat(parseformula("(p→⊥)∨(p→⊥)"), threevaluedalgebra) == true
@test sat(parseformula("p→p"), threevaluedalgebra) == true
@test sat(parseformula("p→(p→⊥)"), threevaluedalgebra) == true
@test sat(parseformula("(p→⊥)→p"), threevaluedalgebra) == true
@test sat(parseformula("(p→⊥)→(p→⊥)"), threevaluedalgebra) == true

@test sat(parseformula("p"), diamondalgebra) == true
@test sat(parseformula("p→⊥"), diamondalgebra) == true
@test sat(parseformula("p∧p"), diamondalgebra) == true
@test sat(parseformula("p∧(p→⊥)"), diamondalgebra) == false
@test sat(parseformula("(p→⊥)∧p"), diamondalgebra) == false
@test sat(parseformula("(p→⊥)∧(p→⊥)"), diamondalgebra) == true
@test sat(parseformula("p∨p"), diamondalgebra) == true
@test sat(parseformula("p∨(p→⊥)"), diamondalgebra) == true
@test sat(parseformula("(p→⊥)∨p"), diamondalgebra) == true
@test sat(parseformula("(p→⊥)∨(p→⊥)"), diamondalgebra) == true
@test sat(parseformula("p→p"), diamondalgebra) == true
@test sat(parseformula("p→(p→⊥)"), diamondalgebra) == true
@test sat(parseformula("(p→⊥)→p"), diamondalgebra) == true
@test sat(parseformula("(p→⊥)→(p→⊥)"), diamondalgebra) == true

@test sat(
    parseformula(
        "(x∨y∨z)∧(x∨y∨(z→⊥))∧(x∨(y→⊥)∨z)∧(x∨(y→⊥)∨(z→⊥))∧" *
        "((x→⊥)∨y∨z)∧((x→⊥)∨y∨(z→⊥))∧((x→⊥)∨(y→⊥)∨z)∧((x→⊥)∨(y→⊥)∨z)"
    ),
    booleanalgebra
) == true

@test sat(
    parseformula(
        "(x∨y∨z)∧(x∨y∨(z→⊥))∧(x∨(y→⊥)∨z)∧(x∨(y→⊥)∨(z→⊥))∧" *
        "((x→⊥)∨y∨z)∧((x→⊥)∨y∨(z→⊥))∧((x→⊥)∨(y→⊥)∨z)∧((x→⊥)∨(y→⊥)∨(z→⊥))"
    ),
    booleanalgebra
) == false

@test sat(
    parseformula(
        "(x∨y∨z)∧(x∨y∨(z→⊥))∧(x∨(y→⊥)∨z)∧(x∨(y→⊥)∨(z→⊥))∧" *
        "((x→⊥)∨y∨z)∧((x→⊥)∨y∨(z→⊥))∧((x→⊥)∨(y→⊥)∨z)∧((x→⊥)∨(y→⊥)∨z)"
    ),
    threevaluedalgebra
) == true

@test sat(
    parseformula(
        "(x∨y∨z)∧(x∨y∨(z→⊥))∧(x∨(y→⊥)∨z)∧(x∨(y→⊥)∨(z→⊥))∧" *
        "((x→⊥)∨y∨z)∧((x→⊥)∨y∨(z→⊥))∧((x→⊥)∨(y→⊥)∨z)∧((x→⊥)∨(y→⊥)∨(z→⊥))"
    ),
    threevaluedalgebra
) == false

@test sat(
    parseformula(
        "(x∨y∨z)∧(x∨y∨(z→⊥))∧(x∨(y→⊥)∨z)∧(x∨(y→⊥)∨(z→⊥))∧" *
        "((x→⊥)∨y∨z)∧((x→⊥)∨y∨(z→⊥))∧((x→⊥)∨(y→⊥)∨z)∧((x→⊥)∨(y→⊥)∨z)"
    ),
    diamondalgebra
) == true

@test sat(
    parseformula(
        "(x∨y∨z)∧(x∨y∨(z→⊥))∧(x∨(y→⊥)∨z)∧(x∨(y→⊥)∨(z→⊥))∧" *
        "((x→⊥)∨y∨z)∧((x→⊥)∨y∨(z→⊥))∧((x→⊥)∨(y→⊥)∨z)∧((x→⊥)∨(y→⊥)∨(z→⊥))"
    ),
    diamondalgebra
) == false

@test sat(
    booleantofuzzy(dimacstosole("benchmark/sat/uf50-01.cnf")),
    booleanalgebra
) == true

@test sat(
    booleantofuzzy(dimacstosole("benchmark/sat/uf50-01.cnf")),
    threevaluedalgebra
) == true

@test sat(
    booleantofuzzy(dimacstosole("benchmark/sat/uf50-01.cnf")),
    diamondalgebra
) == true

@test sat(
    booleantofuzzy(dimacstosole("benchmark/sat/uf50-02.cnf")),
    booleanalgebra
) == true

@test sat(
    booleantofuzzy(dimacstosole("benchmark/sat/uf50-02.cnf")),
    threevaluedalgebra
) == true

@test sat(
    booleantofuzzy(dimacstosole("benchmark/sat/uf50-02.cnf")),
    diamondalgebra
) == true

@test alphasat(⊥, ⊥,       threevaluedalgebra) == true
@test alphasat(⊥, α,       threevaluedalgebra) == true
@test alphasat(⊥, ⊤,       threevaluedalgebra) == true
@test alphasat(⊥, ∧(⊥, ⊥), threevaluedalgebra) == true
@test alphasat(⊥, ∧(⊥, α), threevaluedalgebra) == true
@test alphasat(⊥, ∧(⊥, ⊤), threevaluedalgebra) == true
@test alphasat(⊥, ∧(α, ⊥), threevaluedalgebra) == true
@test alphasat(⊥, ∧(α, α), threevaluedalgebra) == true
@test alphasat(⊥, ∧(α, ⊤), threevaluedalgebra) == true
@test alphasat(⊥, ∧(⊤, ⊥), threevaluedalgebra) == true
@test alphasat(⊥, ∧(⊤, α), threevaluedalgebra) == true
@test alphasat(⊥, ∧(⊤, ⊤), threevaluedalgebra) == true
@test alphasat(⊥, ∨(⊥, ⊥), threevaluedalgebra) == true
@test alphasat(⊥, ∨(⊥, α), threevaluedalgebra) == true
@test alphasat(⊥, ∨(⊥, ⊤), threevaluedalgebra) == true
@test alphasat(⊥, ∨(α, ⊥), threevaluedalgebra) == true
@test alphasat(⊥, ∨(α, α), threevaluedalgebra) == true
@test alphasat(⊥, ∨(α, ⊤), threevaluedalgebra) == true
@test alphasat(⊥, ∨(⊤, ⊥), threevaluedalgebra) == true
@test alphasat(⊥, ∨(⊤, α), threevaluedalgebra) == true
@test alphasat(⊥, ∨(⊤, ⊤), threevaluedalgebra) == true
@test alphasat(⊥, →(⊥, ⊥), threevaluedalgebra) == true
@test alphasat(⊥, →(⊥, α), threevaluedalgebra) == true
@test alphasat(⊥, →(⊥, ⊤), threevaluedalgebra) == true
@test alphasat(⊥, →(α, ⊥), threevaluedalgebra) == true
@test alphasat(⊥, →(α, α), threevaluedalgebra) == true
@test alphasat(⊥, →(α, ⊤), threevaluedalgebra) == true
@test alphasat(⊥, →(⊤, ⊥), threevaluedalgebra) == true
@test alphasat(⊥, →(⊤, α), threevaluedalgebra) == true
@test alphasat(⊥, →(⊤, ⊤), threevaluedalgebra) == true

@test alphasat(α, ⊥,       threevaluedalgebra) == false
@test alphasat(α, α,       threevaluedalgebra) == true
@test alphasat(α, ⊤,       threevaluedalgebra) == true
@test alphasat(α, ∧(⊥, ⊥), threevaluedalgebra) == false
@test alphasat(α, ∧(⊥, α), threevaluedalgebra) == false
@test alphasat(α, ∧(⊥, ⊤), threevaluedalgebra) == false
@test alphasat(α, ∧(α, ⊥), threevaluedalgebra) == false
@test alphasat(α, ∧(α, α), threevaluedalgebra) == true
@test alphasat(α, ∧(α, ⊤), threevaluedalgebra) == true
@test alphasat(α, ∧(⊤, ⊥), threevaluedalgebra) == false
@test alphasat(α, ∧(⊤, α), threevaluedalgebra) == true
@test alphasat(α, ∧(⊤, ⊤), threevaluedalgebra) == true
@test alphasat(α, ∨(⊥, ⊥), threevaluedalgebra) == false
@test alphasat(α, ∨(⊥, α), threevaluedalgebra) == true
@test alphasat(α, ∨(⊥, ⊤), threevaluedalgebra) == true
@test alphasat(α, ∨(α, ⊥), threevaluedalgebra) == true
@test alphasat(α, ∨(α, α), threevaluedalgebra) == true
@test alphasat(α, ∨(α, ⊤), threevaluedalgebra) == true
@test alphasat(α, ∨(⊤, ⊥), threevaluedalgebra) == true
@test alphasat(α, ∨(⊤, α), threevaluedalgebra) == true
@test alphasat(α, ∨(⊤, ⊤), threevaluedalgebra) == true
@test alphasat(α, →(⊥, ⊥), threevaluedalgebra) == true
@test alphasat(α, →(⊥, α), threevaluedalgebra) == true
@test alphasat(α, →(⊥, ⊤), threevaluedalgebra) == true
@test alphasat(α, →(α, ⊥), threevaluedalgebra) == false
@test alphasat(α, →(α, α), threevaluedalgebra) == true
@test alphasat(α, →(α, ⊤), threevaluedalgebra) == true
@test alphasat(α, →(⊤, ⊥), threevaluedalgebra) == false
@test alphasat(α, →(⊤, α), threevaluedalgebra) == true
@test alphasat(α, →(⊤, ⊤), threevaluedalgebra) == true

@test alphasat(⊤, ⊥,       threevaluedalgebra) == false
@test alphasat(⊤, α,       threevaluedalgebra) == false
@test alphasat(⊤, ⊤,       threevaluedalgebra) == true
@test alphasat(⊤, ∧(⊥, ⊥), threevaluedalgebra) == false
@test alphasat(⊤, ∧(⊥, α), threevaluedalgebra) == false
@test alphasat(⊤, ∧(⊥, ⊤), threevaluedalgebra) == false
@test alphasat(⊤, ∧(α, ⊥), threevaluedalgebra) == false
@test alphasat(⊤, ∧(α, α), threevaluedalgebra) == false
@test alphasat(⊤, ∧(α, ⊤), threevaluedalgebra) == false
@test alphasat(⊤, ∧(⊤, ⊥), threevaluedalgebra) == false
@test alphasat(⊤, ∧(⊤, α), threevaluedalgebra) == false
@test alphasat(⊤, ∧(⊤, ⊤), threevaluedalgebra) == true
@test alphasat(⊤, ∨(⊥, ⊥), threevaluedalgebra) == false
@test alphasat(⊤, ∨(⊥, α), threevaluedalgebra) == false
@test alphasat(⊤, ∨(⊥, ⊤), threevaluedalgebra) == true
@test alphasat(⊤, ∨(α, ⊥), threevaluedalgebra) == false
@test alphasat(⊤, ∨(α, α), threevaluedalgebra) == false
@test alphasat(⊤, ∨(α, ⊤), threevaluedalgebra) == true
@test alphasat(⊤, ∨(⊤, ⊥), threevaluedalgebra) == true
@test alphasat(⊤, ∨(⊤, α), threevaluedalgebra) == true
@test alphasat(⊤, ∨(⊤, ⊤), threevaluedalgebra) == true
@test alphasat(⊤, →(⊥, ⊥), threevaluedalgebra) == true
@test alphasat(⊤, →(⊥, α), threevaluedalgebra) == true
@test alphasat(⊤, →(⊥, ⊤), threevaluedalgebra) == true
@test alphasat(⊤, →(α, ⊥), threevaluedalgebra) == true
@test alphasat(⊤, →(α, α), threevaluedalgebra) == true
@test alphasat(⊤, →(α, ⊤), threevaluedalgebra) == true
@test alphasat(⊤, →(⊤, ⊥), threevaluedalgebra) == false
@test alphasat(⊤, →(⊤, α), threevaluedalgebra) == false
@test alphasat(⊤, →(⊤, ⊤), threevaluedalgebra) == true

@test alphasat(
    α,
    →(
        ∧(
            →(
                α,
                Atom("A")
            ),
            →(
                ⊤,
                →(
                    Atom("A"),
                    Atom("B")
                )
            )
        ),
        Atom("B")
    ),
    threevaluedalgebra
) == true
