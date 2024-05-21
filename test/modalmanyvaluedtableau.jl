using SoleLogics
using SoleReasoners
using Test

using SoleLogics.ManyValuedLogics: G3
using SoleLogics.ManyValuedLogics: α
using SoleReasoners: alphaprove2

X, Y = Atom.(["X", "Y"])
@test alphaprove2(α, parseformula("((α→◊X)∧(⊤→□Y))→◊(X∧Y)"), G3, verbose=true) == true
