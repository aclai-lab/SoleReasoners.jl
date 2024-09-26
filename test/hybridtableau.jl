using SoleLogics
using SoleLogics.ManyValuedLogics
using SoleLogics.ManyValuedLogics: G4
using SoleReasoners

alphahybridsat(⊤, booleantofuzzy(parseformula(
           "(x∨y∨z)∧(x∨y∨¬z)∧(x∨¬y∨z)∧(x∨¬y∨¬z)∧(¬x∨y∨z)∧(¬x∨y∨¬z)∧(¬x∨¬y∨z)∧(¬x∨¬y∨¬z)"
       )), G4)
