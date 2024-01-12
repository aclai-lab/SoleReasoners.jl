using SoleReasoners

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

@atoms p q r

@test sat(∧(p,q,r)) == true

@test sat(parseformula("p∧q"))   == true
@test sat(parseformula("p∧¬p"))  == false
@test sat(parseformula("p∧¬¬p")) == true

@test sat(parseformula("¬(p∧q)"))  == true
@test sat(parseformula("p∧¬p"))    == false
@test sat(parseformula("¬(p∧¬p)")) == true

@test sat(parseformula("p→q"))  == true
@test sat(parseformula("p→¬p")) == true
@test sat(parseformula("¬p→p")) == true

@test sat(parseformula("(x∨y∨z)∧(x∨y∨¬z)∧(x∨¬y∨z)∧(x∨¬y∨¬z)∧(¬x∨y∨z)∧(¬x∨y∨¬z)∧(¬x∨¬y∨z)∧(¬x∨¬y∨z)"))  == true
@test sat(parseformula("(x∨y∨z)∧(x∨y∨¬z)∧(x∨¬y∨z)∧(x∨¬y∨¬z)∧(¬x∨y∨z)∧(¬x∨y∨¬z)∧(¬x∨¬y∨z)∧(¬x∨¬y∨¬z)")) == false
