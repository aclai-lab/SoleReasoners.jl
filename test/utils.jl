@test booleantofuzzy(
    parseformula(
        "(x∨y∨z)∧(x∨y∨¬z)∧(x∨¬y∨z)∧(x∨¬y∨¬z)∧(¬x∨y∨z)∧(¬x∨y∨¬z)∧(¬x∨¬y∨z)∧(¬x∨¬y∨¬z)"
    )
) == parseformula(
    "(x∨y∨z)∧(x∨y∨(z→⊥))∧(x∨(y→⊥)∨z)∧(x∨(y→⊥)∨(z→⊥))∧"*
    "((x→⊥)∨y∨z)∧((x→⊥)∨y∨(z→⊥))∧((x→⊥)∨(y→⊥)∨z)∧((x→⊥)∨(y→⊥)∨(z→⊥))"
)
