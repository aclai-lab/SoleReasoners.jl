using SoleReasoners

booleanalgebra = @heytingalgebra () (⊥, ⊤)
myalgebra = @heytingalgebra (α,) (⊥, α) (α, ⊤)

@test fuzzysat(parseformula("⊥"), booleanalgebra) == false
@test fuzzysat(parseformula("⊤"), booleanalgebra) == true
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

@test fuzzysat(parseformula("⊥"), myalgebra) == false
@test fuzzysat(parseformula("⊤"), myalgebra) == true
@test fuzzysat(parseformula("⊥∧⊥"), myalgebra) == false
@test fuzzysat(parseformula("⊥∧⊤"), myalgebra) == false
@test fuzzysat(parseformula("⊤∧⊥"), myalgebra) == false
@test fuzzysat(parseformula("⊤∧⊤"), myalgebra) == true
@test fuzzysat(parseformula("⊥∨⊥"), myalgebra) == false
@test fuzzysat(parseformula("⊥∨⊤"), myalgebra) == true
@test fuzzysat(parseformula("⊤∨⊥"), myalgebra) == true
@test fuzzysat(parseformula("⊤∨⊤"), myalgebra) == true
@test fuzzysat(parseformula("⊥→⊥"), myalgebra) == true
@test fuzzysat(parseformula("⊥→⊤"), myalgebra) == true
@test fuzzysat(parseformula("⊤→⊥"), myalgebra) == false
@test fuzzysat(parseformula("⊤→⊤"), myalgebra) == true

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

@test fuzzysat(parseformula("p"), myalgebra) == true
@test fuzzysat(parseformula("p→⊥"), myalgebra) == true
@test fuzzysat(parseformula("p∧p"), myalgebra) == true
@test fuzzysat(parseformula("p∧(p→⊥)"), myalgebra) == false
@test fuzzysat(parseformula("(p→⊥)∧p"), myalgebra) == false
@test fuzzysat(parseformula("(p→⊥)∧(p→⊥)"), myalgebra) == true
@test fuzzysat(parseformula("p∨p"), myalgebra) == true
@test fuzzysat(parseformula("p∨(p→⊥)"), myalgebra) == true
@test fuzzysat(parseformula("(p→⊥)∨p"), myalgebra) == true
@test fuzzysat(parseformula("(p→⊥)∨(p→⊥)"), myalgebra) == true
@test fuzzysat(parseformula("p→p"), myalgebra) == true
@test fuzzysat(parseformula("p→(p→⊥)"), myalgebra) == true
@test fuzzysat(parseformula("(p→⊥)→p"), myalgebra) == true
@test fuzzysat(parseformula("(p→⊥)→(p→⊥)"), myalgebra) == true

@test fuzzysat(parseformula("(x∨y∨z)∧(x∨y∨(z→⊥))∧(x∨(y→⊥)∨z)∧(x∨(y→⊥)∨(z→⊥))∧((x→⊥)∨y∨z)∧((x→⊥)∨y∨(z→⊥))∧((x→⊥)∨(y→⊥)∨z)∧((x→⊥)∨(y→⊥)∨z)"), booleanalgebra) == true
@test fuzzysat(parseformula("(x∨y∨z)∧(x∨y∨(z→⊥))∧(x∨(y→⊥)∨z)∧(x∨(y→⊥)∨(z→⊥))∧((x→⊥)∨y∨z)∧((x→⊥)∨y∨(z→⊥))∧((x→⊥)∨(y→⊥)∨z)∧((x→⊥)∨(y→⊥)∨(z→⊥))"), booleanalgebra) == false

@test fuzzysat(parseformula("(x∨y∨z)∧(x∨y∨(z→⊥))∧(x∨(y→⊥)∨z)∧(x∨(y→⊥)∨(z→⊥))∧((x→⊥)∨y∨z)∧((x→⊥)∨y∨(z→⊥))∧((x→⊥)∨(y→⊥)∨z)∧((x→⊥)∨(y→⊥)∨z)"), myalgebra) == true
@test fuzzysat(parseformula("(x∨y∨z)∧(x∨y∨(z→⊥))∧(x∨(y→⊥)∨z)∧(x∨(y→⊥)∨(z→⊥))∧((x→⊥)∨y∨z)∧((x→⊥)∨y∨(z→⊥))∧((x→⊥)∨(y→⊥)∨z)∧((x→⊥)∨(y→⊥)∨(z→⊥))"), myalgebra) == false

@test fuzzysat(booleantofuzzy(dimacstosole("benchmark/sat/uf50-01.cnf")), booleanalgebra) == true
@test fuzzysat(booleantofuzzy(dimacstosole("benchmark/sat/uf50-01.cnf")), myalgebra) == true
