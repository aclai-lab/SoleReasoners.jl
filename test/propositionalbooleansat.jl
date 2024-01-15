using SoleReasoners

@test sat(parseformula("⊥∧⊥"))  == true
@test sat(parseformula("⊥∧⊤"))  == true
@test sat(parseformula("⊤∧⊥"))  == true
@test sat(parseformula("⊤∧⊤"))  == true
@test sat(parseformula("⊥∨⊥"))  == true
@test sat(parseformula("⊥∨⊤"))  == true
@test sat(parseformula("⊤∨⊥"))  == true
@test sat(parseformula("⊤∨⊤"))  == true
@test sat(parseformula("⊥→⊥"))  == true
@test sat(parseformula("⊥→⊤"))  == true
@test sat(parseformula("⊤→⊥"))  == true
@test sat(parseformula("⊤→⊤"))  == true
@test sat(parseformula("¬⊥"))   == true
@test sat(parseformula("¬⊤"))   == true

@test sat(parseformula("p∨(p∨(p∨q)∨q∨(p∨(p∨q)))")) == true
@test sat(parseformula("p∨q"))                     == true
@test sat(parseformula("p∧((¬p∧q∧s)∨(p∧r∧t))"))    == true
@test sat(parseformula("(¬p∨q∧¬q∧s)∨(p∧r)"))       == true
@test sat(parseformula("p∧q∧r∧s"))                 == true
@test sat(parseformula("p∧¬p"))                    == false

@test sat(parseformula("p"))    == true
@test sat(parseformula("p∧q"))  == true
@test sat(parseformula("p∨q"))  == true
@test sat(parseformula("p∧¬p")) == false
@test sat(parseformula("¬p∧p")) == false
@test sat(parseformula("p∨¬p")) == true
@test sat(parseformula("¬p∨p")) == true

@test sat(parseformula("p∧q"))   == true
@test sat(parseformula("p∧¬p"))  == false
@test sat(parseformula("p∧¬¬p")) == true

@test sat(parseformula("¬(p∧q)"))  == true
@test sat(parseformula("p∧¬p"))    == false
@test sat(parseformula("¬(p∧¬p)")) == true

@test sat(parseformula("p→q"))  == true
@test sat(parseformula("p→¬p")) == true
@test sat(parseformula("¬p→p")) == true

@test sat(parseformula("(x∨y∨z)∧(x∨y∨¬z)∧(x∨¬y∨z)∧(x∨¬y∨¬z)∧(¬x∨y∨z)∧(¬x∨y∨¬z)∧(¬x∨¬y∨z)∧(¬x∨¬y∨¬z)")) == false

@test sat(dimacstosole("benchmark/uf50-01.cnf")) == true
@test sat(dimacstosole("benchmark/uf50-01.cnf"), naivechooseleaf) == true
