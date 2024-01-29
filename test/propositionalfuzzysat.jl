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

@test fuzzysat(parseformula("⊥"),   booleanalgebra) == false
@test fuzzysat(parseformula("⊤"),   booleanalgebra) == true
@test fuzzysat(parseformula("⊥∧⊥"), booleanalgebra) == false
@test fuzzysat(parseformula("⊥∧⊤"), booleanalgebra) == false
@test fuzzysat(parseformula("⊤∧⊥"), booleanalgebra) == false
@test fuzzysat(parseformula("⊤∧⊤"), booleanalgebra) == true
@test fuzzysat(parseformula("⊥∨⊥"), booleanalgebra) == false
@test fuzzysat(parseformula("⊥∨⊤"), booleanalgebra) == true
@test fuzzysat(parseformula("⊤∨⊥"), booleanalgebra) == true
@test fuzzysat(parseformula("⊤∨⊤"), booleanalgebra) == true
@test fuzzysat(parseformula("⊥→⊥"), booleanalgebra) == true
@test fuzzysat(parseformula("⊥→⊤"), booleanalgebra) == true
@test fuzzysat(parseformula("⊤→⊥"), booleanalgebra) == false
@test fuzzysat(parseformula("⊤→⊤"), booleanalgebra) == true

@test fuzzysat(parseformula("⊥"),   threevaluedalgebra) == false
@test fuzzysat(parseformula("⊤"),   threevaluedalgebra) == true
@test fuzzysat(parseformula("⊥∧⊥"), threevaluedalgebra) == false
@test fuzzysat(parseformula("⊥∧⊤"), threevaluedalgebra) == false
@test fuzzysat(parseformula("⊤∧⊥"), threevaluedalgebra) == false
@test fuzzysat(parseformula("⊤∧⊤"), threevaluedalgebra) == true
@test fuzzysat(parseformula("⊥∨⊥"), threevaluedalgebra) == false
@test fuzzysat(parseformula("⊥∨⊤"), threevaluedalgebra) == true
@test fuzzysat(parseformula("⊤∨⊥"), threevaluedalgebra) == true
@test fuzzysat(parseformula("⊤∨⊤"), threevaluedalgebra) == true
@test fuzzysat(parseformula("⊥→⊥"), threevaluedalgebra) == true
@test fuzzysat(parseformula("⊥→⊤"), threevaluedalgebra) == true
@test fuzzysat(parseformula("⊤→⊥"), threevaluedalgebra) == false
@test fuzzysat(parseformula("⊤→⊤"), threevaluedalgebra) == true

@test fuzzysat(parseformula("⊥"),   diamondalgebra) == false
@test fuzzysat(parseformula("⊤"),   diamondalgebra) == true
@test fuzzysat(parseformula("⊥∧⊥"), diamondalgebra) == false
@test fuzzysat(parseformula("⊥∧⊤"), diamondalgebra) == false
@test fuzzysat(parseformula("⊤∧⊥"), diamondalgebra) == false
@test fuzzysat(parseformula("⊤∧⊤"), diamondalgebra) == true
@test fuzzysat(parseformula("⊥∨⊥"), diamondalgebra) == false
@test fuzzysat(parseformula("⊥∨⊤"), diamondalgebra) == true
@test fuzzysat(parseformula("⊤∨⊥"), diamondalgebra) == true
@test fuzzysat(parseformula("⊤∨⊤"), diamondalgebra) == true
@test fuzzysat(parseformula("⊥→⊥"), diamondalgebra) == true
@test fuzzysat(parseformula("⊥→⊤"), diamondalgebra) == true
@test fuzzysat(parseformula("⊤→⊥"), diamondalgebra) == false
@test fuzzysat(parseformula("⊤→⊤"), diamondalgebra) == true

@test fuzzysat(parseformula("p"), booleanalgebra) == true
@test fuzzysat(parseformula("p→⊥"), booleanalgebra) == true
@test fuzzysat(parseformula("p∧p"), booleanalgebra) == true
@test fuzzysat(parseformula("p∧(p→⊥)"), booleanalgebra) == false
@test fuzzysat(parseformula("(p→⊥)∧p"), booleanalgebra) == false
@test fuzzysat(parseformula("(p→⊥)∧(p→⊥)"), booleanalgebra) == true
@test fuzzysat(parseformula("p∨p"), booleanalgebra) == true
@test fuzzysat(parseformula("p∨(p→⊥)"), booleanalgebra) == true
@test fuzzysat(parseformula("(p→⊥)∨p"), booleanalgebra) == true
@test fuzzysat(parseformula("(p→⊥)∨(p→⊥)"), booleanalgebra) == true
@test fuzzysat(parseformula("p→p"), booleanalgebra) == true
@test fuzzysat(parseformula("p→(p→⊥)"), booleanalgebra) == true
@test fuzzysat(parseformula("(p→⊥)→p"), booleanalgebra) == true
@test fuzzysat(parseformula("(p→⊥)→(p→⊥)"), booleanalgebra) == true

@test fuzzysat(parseformula("p"), threevaluedalgebra) == true
@test fuzzysat(parseformula("p→⊥"), threevaluedalgebra) == true
@test fuzzysat(parseformula("p∧p"), threevaluedalgebra) == true
@test fuzzysat(parseformula("p∧(p→⊥)"), threevaluedalgebra) == false
@test fuzzysat(parseformula("(p→⊥)∧p"), threevaluedalgebra) == false
@test fuzzysat(parseformula("(p→⊥)∧(p→⊥)"), threevaluedalgebra) == true
@test fuzzysat(parseformula("p∨p"), threevaluedalgebra) == true
@test fuzzysat(parseformula("p∨(p→⊥)"), threevaluedalgebra) == true
@test fuzzysat(parseformula("(p→⊥)∨p"), threevaluedalgebra) == true
@test fuzzysat(parseformula("(p→⊥)∨(p→⊥)"), threevaluedalgebra) == true
@test fuzzysat(parseformula("p→p"), threevaluedalgebra) == true
@test fuzzysat(parseformula("p→(p→⊥)"), threevaluedalgebra) == true
@test fuzzysat(parseformula("(p→⊥)→p"), threevaluedalgebra) == true
@test fuzzysat(parseformula("(p→⊥)→(p→⊥)"), threevaluedalgebra) == true

@test fuzzysat(parseformula("p"), diamondalgebra) == true
@test fuzzysat(parseformula("p→⊥"), diamondalgebra) == true
@test fuzzysat(parseformula("p∧p"), diamondalgebra) == true
@test fuzzysat(parseformula("p∧(p→⊥)"), diamondalgebra) == false
@test fuzzysat(parseformula("(p→⊥)∧p"), diamondalgebra) == false
@test fuzzysat(parseformula("(p→⊥)∧(p→⊥)"), diamondalgebra) == true
@test fuzzysat(parseformula("p∨p"), diamondalgebra) == true
@test fuzzysat(parseformula("p∨(p→⊥)"), diamondalgebra) == true
@test fuzzysat(parseformula("(p→⊥)∨p"), diamondalgebra) == true
@test fuzzysat(parseformula("(p→⊥)∨(p→⊥)"), diamondalgebra) == true
@test fuzzysat(parseformula("p→p"), diamondalgebra) == true
@test fuzzysat(parseformula("p→(p→⊥)"), diamondalgebra) == true
@test fuzzysat(parseformula("(p→⊥)→p"), diamondalgebra) == true
@test fuzzysat(parseformula("(p→⊥)→(p→⊥)"), diamondalgebra) == true

@test fuzzysat(
    parseformula(
        "(x∨y∨z)∧(x∨y∨(z→⊥))∧(x∨(y→⊥)∨z)∧(x∨(y→⊥)∨(z→⊥))∧" *
        "((x→⊥)∨y∨z)∧((x→⊥)∨y∨(z→⊥))∧((x→⊥)∨(y→⊥)∨z)∧((x→⊥)∨(y→⊥)∨z)"
    ),
    booleanalgebra
) == true

@test fuzzysat(
    parseformula(
        "(x∨y∨z)∧(x∨y∨(z→⊥))∧(x∨(y→⊥)∨z)∧(x∨(y→⊥)∨(z→⊥))∧" *
        "((x→⊥)∨y∨z)∧((x→⊥)∨y∨(z→⊥))∧((x→⊥)∨(y→⊥)∨z)∧((x→⊥)∨(y→⊥)∨(z→⊥))"
    ),
    booleanalgebra
) == false

@test fuzzysat(
    parseformula(
        "(x∨y∨z)∧(x∨y∨(z→⊥))∧(x∨(y→⊥)∨z)∧(x∨(y→⊥)∨(z→⊥))∧" *
        "((x→⊥)∨y∨z)∧((x→⊥)∨y∨(z→⊥))∧((x→⊥)∨(y→⊥)∨z)∧((x→⊥)∨(y→⊥)∨z)"
    ),
    threevaluedalgebra
) == true

@test fuzzysat(
    parseformula(
        "(x∨y∨z)∧(x∨y∨(z→⊥))∧(x∨(y→⊥)∨z)∧(x∨(y→⊥)∨(z→⊥))∧" *
        "((x→⊥)∨y∨z)∧((x→⊥)∨y∨(z→⊥))∧((x→⊥)∨(y→⊥)∨z)∧((x→⊥)∨(y→⊥)∨(z→⊥))"
    ),
    threevaluedalgebra
) == false

@test fuzzysat(
    parseformula(
        "(x∨y∨z)∧(x∨y∨(z→⊥))∧(x∨(y→⊥)∨z)∧(x∨(y→⊥)∨(z→⊥))∧" *
        "((x→⊥)∨y∨z)∧((x→⊥)∨y∨(z→⊥))∧((x→⊥)∨(y→⊥)∨z)∧((x→⊥)∨(y→⊥)∨z)"
    ),
    diamondalgebra
) == true

@test fuzzysat(
    parseformula(
        "(x∨y∨z)∧(x∨y∨(z→⊥))∧(x∨(y→⊥)∨z)∧(x∨(y→⊥)∨(z→⊥))∧" *
        "((x→⊥)∨y∨z)∧((x→⊥)∨y∨(z→⊥))∧((x→⊥)∨(y→⊥)∨z)∧((x→⊥)∨(y→⊥)∨(z→⊥))"
    ),
    diamondalgebra
) == false

@test fuzzysat(
    booleantofuzzy(dimacstosole("benchmark/sat/uf50-01.cnf")),
    booleanalgebra
) == true

@test fuzzysat(
    booleantofuzzy(dimacstosole("benchmark/sat/uf50-01.cnf")),
    threevaluedalgebra
) == true

@test fuzzysat(
    booleantofuzzy(dimacstosole("benchmark/sat/uf50-01.cnf")),
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
