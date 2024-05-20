using SoleLogics
using SoleReasoners
using Test

using SoleLogics.ManyValuedLogics: G3
using SoleLogics.ManyValuedLogics: α
using SoleReasoners: alphaprove2

p, q = Atom.(["p", "q"])
@test alphaprove2(α, parseformula("((α→◊p)∧(⊤→□q))→◊(p∧q)"), G3) == true