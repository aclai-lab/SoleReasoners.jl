############################################################################################
#### H4 ####################################################################################
############################################################################################

using SoleLogics.ManyValuedLogics: H4
using SoleLogics.ManyValuedLogics: α, β

diamondA = diamond(IA_A)
boxA = box(IA_A)

############################################################################################
## (Strong) disjuction #####################################################################
############################################################################################

println("A")

@test mvhsalphasat(⊥, ∨(diamondA(⊥), boxA(⊥)), FiniteHeytingAlgebra(H4)) == mvhsalphasat(⊥, ∨(⊥, ⊥), FiniteHeytingAlgebra(H4))
@test mvhsalphasat(⊥, ∨(diamondA(⊥), boxA(α)), FiniteHeytingAlgebra(H4)) == mvhsalphasat(⊥, ∨(⊥, α), FiniteHeytingAlgebra(H4))
@test mvhsalphasat(⊥, ∨(diamondA(⊥), boxA(β)), FiniteHeytingAlgebra(H4)) == mvhsalphasat(⊥, ∨(⊥, β), FiniteHeytingAlgebra(H4))
@test mvhsalphasat(⊥, ∨(diamondA(⊥), boxA(⊤)), FiniteHeytingAlgebra(H4)) == mvhsalphasat(⊥, ∨(⊥, ⊤), FiniteHeytingAlgebra(H4))
@test mvhsalphasat(⊥, ∨(diamondA(α), boxA(⊥)), FiniteHeytingAlgebra(H4)) == mvhsalphasat(⊥, ∨(α, ⊥), FiniteHeytingAlgebra(H4))
@test mvhsalphasat(⊥, ∨(diamondA(α), boxA(α)), FiniteHeytingAlgebra(H4)) == mvhsalphasat(⊥, ∨(α, α), FiniteHeytingAlgebra(H4))
@test mvhsalphasat(⊥, ∨(diamondA(α), boxA(β)), FiniteHeytingAlgebra(H4)) == mvhsalphasat(⊥, ∨(α, β), FiniteHeytingAlgebra(H4))
@test mvhsalphasat(⊥, ∨(diamondA(α), boxA(⊤)), FiniteHeytingAlgebra(H4)) == mvhsalphasat(⊥, ∨(α, ⊤), FiniteHeytingAlgebra(H4))
@test mvhsalphasat(⊥, ∨(diamondA(β), boxA(⊥)), FiniteHeytingAlgebra(H4)) == mvhsalphasat(⊥, ∨(β, ⊥), FiniteHeytingAlgebra(H4))
@test mvhsalphasat(⊥, ∨(diamondA(β), boxA(α)), FiniteHeytingAlgebra(H4)) == mvhsalphasat(⊥, ∨(β, α), FiniteHeytingAlgebra(H4))
@test mvhsalphasat(⊥, ∨(diamondA(β), boxA(β)), FiniteHeytingAlgebra(H4)) == mvhsalphasat(⊥, ∨(β, β), FiniteHeytingAlgebra(H4))
@test mvhsalphasat(⊥, ∨(diamondA(β), boxA(⊤)), FiniteHeytingAlgebra(H4)) == mvhsalphasat(⊥, ∨(β, ⊤), FiniteHeytingAlgebra(H4))
@test mvhsalphasat(⊥, ∨(diamondA(⊤), boxA(⊥)), FiniteHeytingAlgebra(H4)) == mvhsalphasat(⊥, ∨(⊤, ⊥), FiniteHeytingAlgebra(H4))
@test mvhsalphasat(⊥, ∨(diamondA(⊤), boxA(α)), FiniteHeytingAlgebra(H4)) == mvhsalphasat(⊥, ∨(⊤, α), FiniteHeytingAlgebra(H4))
@test mvhsalphasat(⊥, ∨(diamondA(⊤), boxA(β)), FiniteHeytingAlgebra(H4)) == mvhsalphasat(⊥, ∨(⊤, β), FiniteHeytingAlgebra(H4))
@test mvhsalphasat(⊥, ∨(diamondA(⊤), boxA(⊤)), FiniteHeytingAlgebra(H4)) == mvhsalphasat(⊥, ∨(⊤, ⊤), FiniteHeytingAlgebra(H4))

println("B")

println("⊥")
@test mvhsalphasat(α, ∨(diamondA(⊥), boxA(⊥)), FiniteHeytingAlgebra(H4)) == mvhsalphasat(α, ∨(⊥, ⊥), FiniteHeytingAlgebra(H4))
@test mvhsalphasat(α, ∨(diamondA(⊥), boxA(α)), FiniteHeytingAlgebra(H4)) == mvhsalphasat(α, ∨(⊥, α), FiniteHeytingAlgebra(H4))
@test mvhsalphasat(α, ∨(diamondA(⊥), boxA(β)), FiniteHeytingAlgebra(H4)) == mvhsalphasat(α, ∨(⊥, β), FiniteHeytingAlgebra(H4))
@test mvhsalphasat(α, ∨(diamondA(⊥), boxA(⊤)), FiniteHeytingAlgebra(H4)) == mvhsalphasat(α, ∨(⊥, ⊤), FiniteHeytingAlgebra(H4))
println("α")
@test mvhsalphasat(α, ∨(diamondA(α), boxA(⊥)), FiniteHeytingAlgebra(H4)) == mvhsalphasat(α, ∨(α, ⊥), FiniteHeytingAlgebra(H4))
@test mvhsalphasat(α, ∨(diamondA(α), boxA(α)), FiniteHeytingAlgebra(H4)) == mvhsalphasat(α, ∨(α, α), FiniteHeytingAlgebra(H4))
@test mvhsalphasat(α, ∨(diamondA(α), boxA(β)), FiniteHeytingAlgebra(H4)) == mvhsalphasat(α, ∨(α, β), FiniteHeytingAlgebra(H4))
@test mvhsalphasat(α, ∨(diamondA(α), boxA(⊤)), FiniteHeytingAlgebra(H4)) == mvhsalphasat(α, ∨(α, ⊤), FiniteHeytingAlgebra(H4))
println("β")
@test mvhsalphasat(α, ∨(diamondA(β), boxA(⊥)), FiniteHeytingAlgebra(H4)) == mvhsalphasat(α, ∨(β, ⊥), FiniteHeytingAlgebra(H4))
@test mvhsalphasat(α, ∨(diamondA(β), boxA(α)), FiniteHeytingAlgebra(H4)) == mvhsalphasat(α, ∨(β, α), FiniteHeytingAlgebra(H4))
@test mvhsalphasat(α, ∨(diamondA(β), boxA(β)), FiniteHeytingAlgebra(H4)) == mvhsalphasat(α, ∨(β, β), FiniteHeytingAlgebra(H4))
@test mvhsalphasat(α, ∨(diamondA(β), boxA(⊤)), FiniteHeytingAlgebra(H4)) == mvhsalphasat(α, ∨(β, ⊤), FiniteHeytingAlgebra(H4))
println("⊤")
@test mvhsalphasat(α, ∨(diamondA(⊤), boxA(⊥)), FiniteHeytingAlgebra(H4)) == mvhsalphasat(α, ∨(⊤, ⊥), FiniteHeytingAlgebra(H4))
@test mvhsalphasat(α, ∨(diamondA(⊤), boxA(α)), FiniteHeytingAlgebra(H4)) == mvhsalphasat(α, ∨(⊤, α), FiniteHeytingAlgebra(H4))
@test mvhsalphasat(α, ∨(diamondA(⊤), boxA(β)), FiniteHeytingAlgebra(H4)) == mvhsalphasat(α, ∨(⊤, β), FiniteHeytingAlgebra(H4))
@test mvhsalphasat(α, ∨(diamondA(⊤), boxA(⊤)), FiniteHeytingAlgebra(H4)) == mvhsalphasat(α, ∨(⊤, ⊤), FiniteHeytingAlgebra(H4))

println("C")

@test mvhsalphasat(β, ∨(diamondA(⊥), boxA(⊥)), FiniteHeytingAlgebra(H4)) == mvhsalphasat(β, ∨(⊥, ⊥), FiniteHeytingAlgebra(H4))
@test mvhsalphasat(β, ∨(diamondA(⊥), boxA(α)), FiniteHeytingAlgebra(H4)) == mvhsalphasat(β, ∨(⊥, α), FiniteHeytingAlgebra(H4))
@test mvhsalphasat(β, ∨(diamondA(⊥), boxA(β)), FiniteHeytingAlgebra(H4)) == mvhsalphasat(β, ∨(⊥, β), FiniteHeytingAlgebra(H4))
@test mvhsalphasat(β, ∨(diamondA(⊥), boxA(⊤)), FiniteHeytingAlgebra(H4)) == mvhsalphasat(β, ∨(⊥, ⊤), FiniteHeytingAlgebra(H4))
@test mvhsalphasat(β, ∨(diamondA(α), boxA(⊥)), FiniteHeytingAlgebra(H4)) == mvhsalphasat(β, ∨(α, ⊥), FiniteHeytingAlgebra(H4))
@test mvhsalphasat(β, ∨(diamondA(α), boxA(α)), FiniteHeytingAlgebra(H4)) == mvhsalphasat(β, ∨(α, α), FiniteHeytingAlgebra(H4))
@test mvhsalphasat(β, ∨(diamondA(α), boxA(β)), FiniteHeytingAlgebra(H4)) == mvhsalphasat(β, ∨(α, β), FiniteHeytingAlgebra(H4))
@test mvhsalphasat(β, ∨(diamondA(α), boxA(⊤)), FiniteHeytingAlgebra(H4)) == mvhsalphasat(β, ∨(α, ⊤), FiniteHeytingAlgebra(H4))
@test mvhsalphasat(β, ∨(diamondA(β), boxA(⊥)), FiniteHeytingAlgebra(H4)) == mvhsalphasat(β, ∨(β, ⊥), FiniteHeytingAlgebra(H4))
@test mvhsalphasat(β, ∨(diamondA(β), boxA(α)), FiniteHeytingAlgebra(H4)) == mvhsalphasat(β, ∨(β, α), FiniteHeytingAlgebra(H4))
@test mvhsalphasat(β, ∨(diamondA(β), boxA(β)), FiniteHeytingAlgebra(H4)) == mvhsalphasat(β, ∨(β, β), FiniteHeytingAlgebra(H4))
@test mvhsalphasat(β, ∨(diamondA(β), boxA(⊤)), FiniteHeytingAlgebra(H4)) == mvhsalphasat(β, ∨(β, ⊤), FiniteHeytingAlgebra(H4))
@test mvhsalphasat(β, ∨(diamondA(⊤), boxA(⊥)), FiniteHeytingAlgebra(H4)) == mvhsalphasat(β, ∨(⊤, ⊥), FiniteHeytingAlgebra(H4))
@test mvhsalphasat(β, ∨(diamondA(⊤), boxA(α)), FiniteHeytingAlgebra(H4)) == mvhsalphasat(β, ∨(⊤, α), FiniteHeytingAlgebra(H4))
@test mvhsalphasat(β, ∨(diamondA(⊤), boxA(β)), FiniteHeytingAlgebra(H4)) == mvhsalphasat(β, ∨(⊤, β), FiniteHeytingAlgebra(H4))
@test mvhsalphasat(β, ∨(diamondA(⊤), boxA(⊤)), FiniteHeytingAlgebra(H4)) == mvhsalphasat(β, ∨(⊤, ⊤), FiniteHeytingAlgebra(H4))

println("D")

@test mvhsalphasat(⊤, ∨(diamondA(⊥), boxA(⊥)), FiniteHeytingAlgebra(H4)) == mvhsalphasat(⊤, ∨(⊥, ⊥), FiniteHeytingAlgebra(H4))
@test mvhsalphasat(⊤, ∨(diamondA(⊥), boxA(α)), FiniteHeytingAlgebra(H4)) == mvhsalphasat(⊤, ∨(⊥, α), FiniteHeytingAlgebra(H4))
@test mvhsalphasat(⊤, ∨(diamondA(⊥), boxA(β)), FiniteHeytingAlgebra(H4)) == mvhsalphasat(⊤, ∨(⊥, β), FiniteHeytingAlgebra(H4))
@test mvhsalphasat(⊤, ∨(diamondA(⊥), boxA(⊤)), FiniteHeytingAlgebra(H4)) == mvhsalphasat(⊤, ∨(⊥, ⊤), FiniteHeytingAlgebra(H4))
@test mvhsalphasat(⊤, ∨(diamondA(α), boxA(⊥)), FiniteHeytingAlgebra(H4)) == mvhsalphasat(⊤, ∨(α, ⊥), FiniteHeytingAlgebra(H4))
@test mvhsalphasat(⊤, ∨(diamondA(α), boxA(α)), FiniteHeytingAlgebra(H4)) == mvhsalphasat(⊤, ∨(α, α), FiniteHeytingAlgebra(H4))
@test mvhsalphasat(⊤, ∨(diamondA(α), boxA(β)), FiniteHeytingAlgebra(H4)) == mvhsalphasat(⊤, ∨(α, β), FiniteHeytingAlgebra(H4))
@test mvhsalphasat(⊤, ∨(diamondA(α), boxA(⊤)), FiniteHeytingAlgebra(H4)) == mvhsalphasat(⊤, ∨(α, ⊤), FiniteHeytingAlgebra(H4))
@test mvhsalphasat(⊤, ∨(diamondA(β), boxA(⊥)), FiniteHeytingAlgebra(H4)) == mvhsalphasat(⊤, ∨(β, ⊥), FiniteHeytingAlgebra(H4))
@test mvhsalphasat(⊤, ∨(diamondA(β), boxA(α)), FiniteHeytingAlgebra(H4)) == mvhsalphasat(⊤, ∨(β, α), FiniteHeytingAlgebra(H4))
@test mvhsalphasat(⊤, ∨(diamondA(β), boxA(β)), FiniteHeytingAlgebra(H4)) == mvhsalphasat(⊤, ∨(β, β), FiniteHeytingAlgebra(H4))
@test mvhsalphasat(⊤, ∨(diamondA(β), boxA(⊤)), FiniteHeytingAlgebra(H4)) == mvhsalphasat(⊤, ∨(β, ⊤), FiniteHeytingAlgebra(H4))
@test mvhsalphasat(⊤, ∨(diamondA(⊤), boxA(⊥)), FiniteHeytingAlgebra(H4)) == mvhsalphasat(⊤, ∨(⊤, ⊥), FiniteHeytingAlgebra(H4))
@test mvhsalphasat(⊤, ∨(diamondA(⊤), boxA(α)), FiniteHeytingAlgebra(H4)) == mvhsalphasat(⊤, ∨(⊤, α), FiniteHeytingAlgebra(H4))
@test mvhsalphasat(⊤, ∨(diamondA(⊤), boxA(β)), FiniteHeytingAlgebra(H4)) == mvhsalphasat(⊤, ∨(⊤, β), FiniteHeytingAlgebra(H4))
@test mvhsalphasat(⊤, ∨(diamondA(⊤), boxA(⊤)), FiniteHeytingAlgebra(H4)) == mvhsalphasat(⊤, ∨(⊤, ⊤), FiniteHeytingAlgebra(H4))

println("E")

@test mvhsalphasat(⊥, ∨(diamondA(parseformula("p")), boxA(⊥)), FiniteHeytingAlgebra(H4)) == mvhsalphasat(⊥, ∨(parseformula("p"), ⊥), FiniteHeytingAlgebra(H4))
@test mvhsalphasat(⊥, ∨(diamondA(parseformula("p")), boxA(α)), FiniteHeytingAlgebra(H4)) == mvhsalphasat(⊥, ∨(parseformula("p"), α), FiniteHeytingAlgebra(H4))
@test mvhsalphasat(⊥, ∨(diamondA(parseformula("p")), boxA(β)), FiniteHeytingAlgebra(H4)) == mvhsalphasat(⊥, ∨(parseformula("p"), β), FiniteHeytingAlgebra(H4))
@test mvhsalphasat(⊥, ∨(diamondA(parseformula("p")), boxA(⊤)), FiniteHeytingAlgebra(H4)) == mvhsalphasat(⊥, ∨(parseformula("p"), ⊤), FiniteHeytingAlgebra(H4))
@test mvhsalphasat(α, ∨(diamondA(parseformula("p")), boxA(⊥)), FiniteHeytingAlgebra(H4)) == mvhsalphasat(α, ∨(parseformula("p"), ⊥), FiniteHeytingAlgebra(H4))
@test mvhsalphasat(α, ∨(diamondA(parseformula("p")), boxA(α)), FiniteHeytingAlgebra(H4)) == mvhsalphasat(α, ∨(parseformula("p"), α), FiniteHeytingAlgebra(H4))
@test mvhsalphasat(α, ∨(diamondA(parseformula("p")), boxA(β)), FiniteHeytingAlgebra(H4)) == mvhsalphasat(α, ∨(parseformula("p"), β), FiniteHeytingAlgebra(H4))
@test mvhsalphasat(α, ∨(diamondA(parseformula("p")), boxA(⊤)), FiniteHeytingAlgebra(H4)) == mvhsalphasat(α, ∨(parseformula("p"), ⊤), FiniteHeytingAlgebra(H4))
@test mvhsalphasat(β, ∨(diamondA(parseformula("p")), boxA(⊥)), FiniteHeytingAlgebra(H4)) == mvhsalphasat(β, ∨(parseformula("p"), ⊥), FiniteHeytingAlgebra(H4))
@test mvhsalphasat(β, ∨(diamondA(parseformula("p")), boxA(α)), FiniteHeytingAlgebra(H4)) == mvhsalphasat(β, ∨(parseformula("p"), α), FiniteHeytingAlgebra(H4))
@test mvhsalphasat(β, ∨(diamondA(parseformula("p")), boxA(β)), FiniteHeytingAlgebra(H4)) == mvhsalphasat(β, ∨(parseformula("p"), β), FiniteHeytingAlgebra(H4))
@test mvhsalphasat(β, ∨(diamondA(parseformula("p")), boxA(⊤)), FiniteHeytingAlgebra(H4)) == mvhsalphasat(β, ∨(parseformula("p"), ⊤), FiniteHeytingAlgebra(H4))
@test mvhsalphasat(⊤, ∨(diamondA(parseformula("p")), boxA(⊥)), FiniteHeytingAlgebra(H4)) == mvhsalphasat(⊤, ∨(parseformula("p"), ⊥), FiniteHeytingAlgebra(H4))
@test mvhsalphasat(⊤, ∨(diamondA(parseformula("p")), boxA(α)), FiniteHeytingAlgebra(H4)) == mvhsalphasat(⊤, ∨(parseformula("p"), α), FiniteHeytingAlgebra(H4))
@test mvhsalphasat(⊤, ∨(diamondA(parseformula("p")), boxA(β)), FiniteHeytingAlgebra(H4)) == mvhsalphasat(⊤, ∨(parseformula("p"), β), FiniteHeytingAlgebra(H4))
@test mvhsalphasat(⊤, ∨(diamondA(parseformula("p")), boxA(⊤)), FiniteHeytingAlgebra(H4)) == mvhsalphasat(⊤, ∨(parseformula("p"), ⊤), FiniteHeytingAlgebra(H4))

println("F")

@test mvhsalphasat(⊥, ∨(diamondA(⊥), boxA(parseformula("p"))), FiniteHeytingAlgebra(H4)) == mvhsalphasat(⊥, ∨(⊥, parseformula("p")), FiniteHeytingAlgebra(H4))
@test mvhsalphasat(⊥, ∨(diamondA(α), boxA(parseformula("p"))), FiniteHeytingAlgebra(H4)) == mvhsalphasat(⊥, ∨(α, parseformula("p")), FiniteHeytingAlgebra(H4))
@test mvhsalphasat(⊥, ∨(diamondA(β), boxA(parseformula("p"))), FiniteHeytingAlgebra(H4)) == mvhsalphasat(⊥, ∨(β, parseformula("p")), FiniteHeytingAlgebra(H4))
@test mvhsalphasat(⊥, ∨(diamondA(⊤), boxA(parseformula("p"))), FiniteHeytingAlgebra(H4)) == mvhsalphasat(⊥, ∨(⊤, parseformula("p")), FiniteHeytingAlgebra(H4))
@test mvhsalphasat(α, ∨(diamondA(⊥), boxA(parseformula("p"))), FiniteHeytingAlgebra(H4)) == mvhsalphasat(α, ∨(⊥, parseformula("p")), FiniteHeytingAlgebra(H4))
@test mvhsalphasat(α, ∨(diamondA(α), boxA(parseformula("p"))), FiniteHeytingAlgebra(H4)) == mvhsalphasat(α, ∨(α, parseformula("p")), FiniteHeytingAlgebra(H4))
@test mvhsalphasat(α, ∨(diamondA(β), boxA(parseformula("p"))), FiniteHeytingAlgebra(H4)) == mvhsalphasat(α, ∨(β, parseformula("p")), FiniteHeytingAlgebra(H4))
@test mvhsalphasat(α, ∨(diamondA(⊤), boxA(parseformula("p"))), FiniteHeytingAlgebra(H4)) == mvhsalphasat(α, ∨(⊤, parseformula("p")), FiniteHeytingAlgebra(H4))
@test mvhsalphasat(β, ∨(diamondA(⊥), boxA(parseformula("p"))), FiniteHeytingAlgebra(H4)) == mvhsalphasat(β, ∨(⊥, parseformula("p")), FiniteHeytingAlgebra(H4))
@test mvhsalphasat(β, ∨(diamondA(α), boxA(parseformula("p"))), FiniteHeytingAlgebra(H4)) == mvhsalphasat(β, ∨(α, parseformula("p")), FiniteHeytingAlgebra(H4))
@test mvhsalphasat(β, ∨(diamondA(β), boxA(parseformula("p"))), FiniteHeytingAlgebra(H4)) == mvhsalphasat(β, ∨(β, parseformula("p")), FiniteHeytingAlgebra(H4))
@test mvhsalphasat(β, ∨(diamondA(⊤), boxA(parseformula("p"))), FiniteHeytingAlgebra(H4)) == mvhsalphasat(β, ∨(⊤, parseformula("p")), FiniteHeytingAlgebra(H4))
@test mvhsalphasat(⊤, ∨(diamondA(⊥), boxA(parseformula("p"))), FiniteHeytingAlgebra(H4)) == mvhsalphasat(⊤, ∨(⊥, parseformula("p")), FiniteHeytingAlgebra(H4))
@test mvhsalphasat(⊤, ∨(diamondA(α), boxA(parseformula("p"))), FiniteHeytingAlgebra(H4)) == mvhsalphasat(⊤, ∨(α, parseformula("p")), FiniteHeytingAlgebra(H4))
@test mvhsalphasat(⊤, ∨(diamondA(β), boxA(parseformula("p"))), FiniteHeytingAlgebra(H4)) == mvhsalphasat(⊤, ∨(β, parseformula("p")), FiniteHeytingAlgebra(H4))
@test mvhsalphasat(⊤, ∨(diamondA(⊤), boxA(parseformula("p"))), FiniteHeytingAlgebra(H4)) == mvhsalphasat(⊤, ∨(⊤, parseformula("p")), FiniteHeytingAlgebra(H4))

println("G")

@test mvhsalphasat(⊥, ∨(diamondA(parseformula("p")), boxA(parseformula("p"))), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(α, ∨(diamondA(parseformula("p")), boxA(parseformula("p"))), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(β, ∨(diamondA(parseformula("p")), boxA(parseformula("p"))), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(⊤, ∨(diamondA(parseformula("p")), boxA(parseformula("p"))), FiniteHeytingAlgebra(H4)) == true

@test mvhsalphasat(⊥, ∨(diamondA(parseformula("p")), boxA(parseformula("q"))), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(α, ∨(diamondA(parseformula("p")), boxA(parseformula("q"))), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(β, ∨(diamondA(parseformula("p")), boxA(parseformula("q"))), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(⊤, ∨(diamondA(parseformula("p")), boxA(parseformula("q"))), FiniteHeytingAlgebra(H4)) == true

@test mvhsalphasat(⊥, ∨(diamondA(parseformula("q")), boxA(parseformula("q"))), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(α, ∨(diamondA(parseformula("q")), boxA(parseformula("q"))), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(β, ∨(diamondA(parseformula("q")), boxA(parseformula("q"))), FiniteHeytingAlgebra(H4)) == true
@test mvhsalphasat(⊤, ∨(diamondA(parseformula("q")), boxA(parseformula("q"))), FiniteHeytingAlgebra(H4)) == true

# ############################################################################################
# ## (Strong) conjunction ####################################################################
# ############################################################################################

# @test mvhsalphasat(⊥, ∧(⊥, ⊥), FiniteHeytingAlgebra(H4)) == true
# @test mvhsalphasat(⊥, ∧(⊥, α), FiniteHeytingAlgebra(H4)) == true
# @test mvhsalphasat(⊥, ∧(⊥, β), FiniteHeytingAlgebra(H4)) == true
# @test mvhsalphasat(⊥, ∧(⊥, ⊤), FiniteHeytingAlgebra(H4)) == true
# @test mvhsalphasat(⊥, ∧(α, ⊥), FiniteHeytingAlgebra(H4)) == true
# @test mvhsalphasat(⊥, ∧(α, α), FiniteHeytingAlgebra(H4)) == true
# @test mvhsalphasat(⊥, ∧(α, β), FiniteHeytingAlgebra(H4)) == true
# @test mvhsalphasat(⊥, ∧(α, ⊤), FiniteHeytingAlgebra(H4)) == true
# @test mvhsalphasat(⊥, ∧(β, ⊥), FiniteHeytingAlgebra(H4)) == true
# @test mvhsalphasat(⊥, ∧(β, α), FiniteHeytingAlgebra(H4)) == true
# @test mvhsalphasat(⊥, ∧(β, β), FiniteHeytingAlgebra(H4)) == true
# @test mvhsalphasat(⊥, ∧(β, ⊤), FiniteHeytingAlgebra(H4)) == true
# @test mvhsalphasat(⊥, ∧(⊤, ⊥), FiniteHeytingAlgebra(H4)) == true
# @test mvhsalphasat(⊥, ∧(⊤, α), FiniteHeytingAlgebra(H4)) == true
# @test mvhsalphasat(⊥, ∧(⊤, β), FiniteHeytingAlgebra(H4)) == true
# @test mvhsalphasat(⊥, ∧(⊤, ⊤), FiniteHeytingAlgebra(H4)) == true

# @test mvhsalphasat(α, ∧(⊥, ⊥), FiniteHeytingAlgebra(H4)) == false
# @test mvhsalphasat(α, ∧(⊥, α), FiniteHeytingAlgebra(H4)) == false
# @test mvhsalphasat(α, ∧(⊥, β), FiniteHeytingAlgebra(H4)) == false
# @test mvhsalphasat(α, ∧(⊥, ⊤), FiniteHeytingAlgebra(H4)) == false
# @test mvhsalphasat(α, ∧(α, ⊥), FiniteHeytingAlgebra(H4)) == false
# @test mvhsalphasat(α, ∧(α, α), FiniteHeytingAlgebra(H4)) == true
# @test mvhsalphasat(α, ∧(α, β), FiniteHeytingAlgebra(H4)) == false
# @test mvhsalphasat(α, ∧(α, ⊤), FiniteHeytingAlgebra(H4)) == true
# @test mvhsalphasat(α, ∧(β, ⊥), FiniteHeytingAlgebra(H4)) == false
# @test mvhsalphasat(α, ∧(β, α), FiniteHeytingAlgebra(H4)) == false
# @test mvhsalphasat(α, ∧(β, β), FiniteHeytingAlgebra(H4)) == false
# @test mvhsalphasat(α, ∧(β, ⊤), FiniteHeytingAlgebra(H4)) == false
# @test mvhsalphasat(α, ∧(⊤, ⊥), FiniteHeytingAlgebra(H4)) == false
# @test mvhsalphasat(α, ∧(⊤, α), FiniteHeytingAlgebra(H4)) == true
# @test mvhsalphasat(α, ∧(⊤, β), FiniteHeytingAlgebra(H4)) == false
# @test mvhsalphasat(α, ∧(⊤, ⊤), FiniteHeytingAlgebra(H4)) == true

# @test mvhsalphasat(β, ∧(⊥, ⊥), FiniteHeytingAlgebra(H4)) == false
# @test mvhsalphasat(β, ∧(⊥, α), FiniteHeytingAlgebra(H4)) == false
# @test mvhsalphasat(β, ∧(⊥, β), FiniteHeytingAlgebra(H4)) == false
# @test mvhsalphasat(β, ∧(⊥, ⊤), FiniteHeytingAlgebra(H4)) == false
# @test mvhsalphasat(β, ∧(α, ⊥), FiniteHeytingAlgebra(H4)) == false
# @test mvhsalphasat(β, ∧(α, α), FiniteHeytingAlgebra(H4)) == false
# @test mvhsalphasat(β, ∧(α, β), FiniteHeytingAlgebra(H4)) == false
# @test mvhsalphasat(β, ∧(α, ⊤), FiniteHeytingAlgebra(H4)) == false
# @test mvhsalphasat(β, ∧(β, ⊥), FiniteHeytingAlgebra(H4)) == false
# @test mvhsalphasat(β, ∧(β, α), FiniteHeytingAlgebra(H4)) == false
# @test mvhsalphasat(β, ∧(β, β), FiniteHeytingAlgebra(H4)) == true
# @test mvhsalphasat(β, ∧(β, ⊤), FiniteHeytingAlgebra(H4)) == true
# @test mvhsalphasat(β, ∧(⊤, ⊥), FiniteHeytingAlgebra(H4)) == false
# @test mvhsalphasat(β, ∧(⊤, α), FiniteHeytingAlgebra(H4)) == false
# @test mvhsalphasat(β, ∧(⊤, β), FiniteHeytingAlgebra(H4)) == true
# @test mvhsalphasat(β, ∧(⊤, ⊤), FiniteHeytingAlgebra(H4)) == true

# @test mvhsalphasat(⊤, ∧(⊥, ⊥), FiniteHeytingAlgebra(H4)) == false
# @test mvhsalphasat(⊤, ∧(⊥, α), FiniteHeytingAlgebra(H4)) == false
# @test mvhsalphasat(⊤, ∧(⊥, β), FiniteHeytingAlgebra(H4)) == false
# @test mvhsalphasat(⊤, ∧(⊥, ⊤), FiniteHeytingAlgebra(H4)) == false
# @test mvhsalphasat(⊤, ∧(α, ⊥), FiniteHeytingAlgebra(H4)) == false
# @test mvhsalphasat(⊤, ∧(α, α), FiniteHeytingAlgebra(H4)) == false
# @test mvhsalphasat(⊤, ∧(α, β), FiniteHeytingAlgebra(H4)) == false
# @test mvhsalphasat(⊤, ∧(α, ⊤), FiniteHeytingAlgebra(H4)) == false
# @test mvhsalphasat(⊤, ∧(β, ⊥), FiniteHeytingAlgebra(H4)) == false
# @test mvhsalphasat(⊤, ∧(β, α), FiniteHeytingAlgebra(H4)) == false
# @test mvhsalphasat(⊤, ∧(β, β), FiniteHeytingAlgebra(H4)) == false
# @test mvhsalphasat(⊤, ∧(β, ⊤), FiniteHeytingAlgebra(H4)) == false
# @test mvhsalphasat(⊤, ∧(⊤, ⊥), FiniteHeytingAlgebra(H4)) == false
# @test mvhsalphasat(⊤, ∧(⊤, α), FiniteHeytingAlgebra(H4)) == false
# @test mvhsalphasat(⊤, ∧(⊤, β), FiniteHeytingAlgebra(H4)) == false
# @test mvhsalphasat(⊤, ∧(⊤, ⊤), FiniteHeytingAlgebra(H4)) == true

# @test mvhsalphasat(⊥, ∧(parseformula("p"), ⊥), FiniteHeytingAlgebra(H4)) == true
# @test mvhsalphasat(⊥, ∧(parseformula("p"), α), FiniteHeytingAlgebra(H4)) == true
# @test mvhsalphasat(⊥, ∧(parseformula("p"), β), FiniteHeytingAlgebra(H4)) == true
# @test mvhsalphasat(⊥, ∧(parseformula("p"), ⊤), FiniteHeytingAlgebra(H4)) == true
# @test mvhsalphasat(α, ∧(parseformula("p"), ⊥), FiniteHeytingAlgebra(H4)) == false
# @test mvhsalphasat(α, ∧(parseformula("p"), α), FiniteHeytingAlgebra(H4)) == true
# @test mvhsalphasat(α, ∧(parseformula("p"), β), FiniteHeytingAlgebra(H4)) == false
# @test mvhsalphasat(α, ∧(parseformula("p"), ⊤), FiniteHeytingAlgebra(H4)) == true
# @test mvhsalphasat(β, ∧(parseformula("p"), ⊥), FiniteHeytingAlgebra(H4)) == false
# @test mvhsalphasat(β, ∧(parseformula("p"), α), FiniteHeytingAlgebra(H4)) == false
# @test mvhsalphasat(β, ∧(parseformula("p"), β), FiniteHeytingAlgebra(H4)) == true
# @test mvhsalphasat(β, ∧(parseformula("p"), ⊤), FiniteHeytingAlgebra(H4)) == true
# @test mvhsalphasat(⊤, ∧(parseformula("p"), ⊥), FiniteHeytingAlgebra(H4)) == false
# @test mvhsalphasat(⊤, ∧(parseformula("p"), α), FiniteHeytingAlgebra(H4)) == false
# @test mvhsalphasat(⊤, ∧(parseformula("p"), β), FiniteHeytingAlgebra(H4)) == false
# @test mvhsalphasat(⊤, ∧(parseformula("p"), ⊤), FiniteHeytingAlgebra(H4)) == true

# @test mvhsalphasat(⊥, ∧(⊥, parseformula("p")), FiniteHeytingAlgebra(H4)) == true
# @test mvhsalphasat(⊥, ∧(α, parseformula("p")), FiniteHeytingAlgebra(H4)) == true
# @test mvhsalphasat(⊥, ∧(β, parseformula("p")), FiniteHeytingAlgebra(H4)) == true
# @test mvhsalphasat(⊥, ∧(⊤, parseformula("p")), FiniteHeytingAlgebra(H4)) == true
# @test mvhsalphasat(α, ∧(⊥, parseformula("p")), FiniteHeytingAlgebra(H4)) == false
# @test mvhsalphasat(α, ∧(α, parseformula("p")), FiniteHeytingAlgebra(H4)) == true
# @test mvhsalphasat(α, ∧(β, parseformula("p")), FiniteHeytingAlgebra(H4)) == false
# @test mvhsalphasat(α, ∧(⊤, parseformula("p")), FiniteHeytingAlgebra(H4)) == true
# @test mvhsalphasat(β, ∧(⊥, parseformula("p")), FiniteHeytingAlgebra(H4)) == false
# @test mvhsalphasat(β, ∧(α, parseformula("p")), FiniteHeytingAlgebra(H4)) == false
# @test mvhsalphasat(β, ∧(β, parseformula("p")), FiniteHeytingAlgebra(H4)) == true
# @test mvhsalphasat(β, ∧(⊤, parseformula("p")), FiniteHeytingAlgebra(H4)) == true
# @test mvhsalphasat(⊤, ∧(⊥, parseformula("p")), FiniteHeytingAlgebra(H4)) == false
# @test mvhsalphasat(⊤, ∧(α, parseformula("p")), FiniteHeytingAlgebra(H4)) == false
# @test mvhsalphasat(⊤, ∧(β, parseformula("p")), FiniteHeytingAlgebra(H4)) == false
# @test mvhsalphasat(⊤, ∧(⊤, parseformula("p")), FiniteHeytingAlgebra(H4)) == true

# @test mvhsalphasat(⊥, ∧(parseformula("p"), parseformula("p")), FiniteHeytingAlgebra(H4)) == true
# @test mvhsalphasat(α, ∧(parseformula("p"), parseformula("p")), FiniteHeytingAlgebra(H4)) == true
# @test mvhsalphasat(β, ∧(parseformula("p"), parseformula("p")), FiniteHeytingAlgebra(H4)) == true
# @test mvhsalphasat(⊤, ∧(parseformula("p"), parseformula("p")), FiniteHeytingAlgebra(H4)) == true

# @test mvhsalphasat(⊥, ∧(parseformula("p"), parseformula("q")), FiniteHeytingAlgebra(H4)) == true
# @test mvhsalphasat(α, ∧(parseformula("p"), parseformula("q")), FiniteHeytingAlgebra(H4)) == true
# @test mvhsalphasat(β, ∧(parseformula("p"), parseformula("q")), FiniteHeytingAlgebra(H4)) == true
# @test mvhsalphasat(⊤, ∧(parseformula("p"), parseformula("q")), FiniteHeytingAlgebra(H4)) == true

# @test mvhsalphasat(⊥, ∧(parseformula("q"), parseformula("p")), FiniteHeytingAlgebra(H4)) == true
# @test mvhsalphasat(α, ∧(parseformula("q"), parseformula("p")), FiniteHeytingAlgebra(H4)) == true
# @test mvhsalphasat(β, ∧(parseformula("q"), parseformula("p")), FiniteHeytingAlgebra(H4)) == true
# @test mvhsalphasat(⊤, ∧(parseformula("q"), parseformula("p")), FiniteHeytingAlgebra(H4)) == true

# ############################################################################################
# ## Implication #############################################################################
# ############################################################################################

# @test mvhsalphasat(⊥, →(⊥, ⊥), FiniteHeytingAlgebra(H4)) == true
# @test mvhsalphasat(⊥, →(⊥, α), FiniteHeytingAlgebra(H4)) == true
# @test mvhsalphasat(⊥, →(⊥, β), FiniteHeytingAlgebra(H4)) == true
# @test mvhsalphasat(⊥, →(⊥, ⊤), FiniteHeytingAlgebra(H4)) == true
# @test mvhsalphasat(⊥, →(α, ⊥), FiniteHeytingAlgebra(H4)) == true
# @test mvhsalphasat(⊥, →(α, α), FiniteHeytingAlgebra(H4)) == true
# @test mvhsalphasat(⊥, →(α, β), FiniteHeytingAlgebra(H4)) == true
# @test mvhsalphasat(⊥, →(α, ⊤), FiniteHeytingAlgebra(H4)) == true
# @test mvhsalphasat(⊥, →(β, ⊥), FiniteHeytingAlgebra(H4)) == true
# @test mvhsalphasat(⊥, →(β, α), FiniteHeytingAlgebra(H4)) == true
# @test mvhsalphasat(⊥, →(β, β), FiniteHeytingAlgebra(H4)) == true
# @test mvhsalphasat(⊥, →(β, ⊤), FiniteHeytingAlgebra(H4)) == true
# @test mvhsalphasat(⊥, →(⊤, ⊥), FiniteHeytingAlgebra(H4)) == true
# @test mvhsalphasat(⊥, →(⊤, α), FiniteHeytingAlgebra(H4)) == true
# @test mvhsalphasat(⊥, →(⊤, β), FiniteHeytingAlgebra(H4)) == true
# @test mvhsalphasat(⊥, →(⊤, ⊤), FiniteHeytingAlgebra(H4)) == true

# @test mvhsalphasat(α, →(⊥, ⊥), FiniteHeytingAlgebra(H4)) == true
# @test mvhsalphasat(α, →(⊥, α), FiniteHeytingAlgebra(H4)) == true
# @test mvhsalphasat(α, →(⊥, β), FiniteHeytingAlgebra(H4)) == true
# @test mvhsalphasat(α, →(⊥, ⊤), FiniteHeytingAlgebra(H4)) == true
# @test mvhsalphasat(α, →(α, ⊥), FiniteHeytingAlgebra(H4)) == false
# @test mvhsalphasat(α, →(α, α), FiniteHeytingAlgebra(H4)) == true
# @test mvhsalphasat(α, →(α, β), FiniteHeytingAlgebra(H4)) == false
# @test mvhsalphasat(α, →(α, ⊤), FiniteHeytingAlgebra(H4)) == true
# @test mvhsalphasat(α, →(β, ⊥), FiniteHeytingAlgebra(H4)) == true
# @test mvhsalphasat(α, →(β, α), FiniteHeytingAlgebra(H4)) == true
# @test mvhsalphasat(α, →(β, β), FiniteHeytingAlgebra(H4)) == true
# @test mvhsalphasat(α, →(β, ⊤), FiniteHeytingAlgebra(H4)) == true
# @test mvhsalphasat(α, →(⊤, ⊥), FiniteHeytingAlgebra(H4)) == false
# @test mvhsalphasat(α, →(⊤, α), FiniteHeytingAlgebra(H4)) == true
# @test mvhsalphasat(α, →(⊤, β), FiniteHeytingAlgebra(H4)) == false
# @test mvhsalphasat(α, →(⊤, ⊤), FiniteHeytingAlgebra(H4)) == true

# @test mvhsalphasat(β, →(⊥, ⊥), FiniteHeytingAlgebra(H4)) == true
# @test mvhsalphasat(β, →(⊥, α), FiniteHeytingAlgebra(H4)) == true
# @test mvhsalphasat(β, →(⊥, β), FiniteHeytingAlgebra(H4)) == true
# @test mvhsalphasat(β, →(⊥, ⊤), FiniteHeytingAlgebra(H4)) == true
# @test mvhsalphasat(β, →(α, ⊥), FiniteHeytingAlgebra(H4)) == true
# @test mvhsalphasat(β, →(α, α), FiniteHeytingAlgebra(H4)) == true
# @test mvhsalphasat(β, →(α, β), FiniteHeytingAlgebra(H4)) == true
# @test mvhsalphasat(β, →(α, ⊤), FiniteHeytingAlgebra(H4)) == true
# @test mvhsalphasat(β, →(β, ⊥), FiniteHeytingAlgebra(H4)) == false
# @test mvhsalphasat(β, →(β, α), FiniteHeytingAlgebra(H4)) == false
# @test mvhsalphasat(β, →(β, β), FiniteHeytingAlgebra(H4)) == true
# @test mvhsalphasat(β, →(β, ⊤), FiniteHeytingAlgebra(H4)) == true
# @test mvhsalphasat(β, →(⊤, ⊥), FiniteHeytingAlgebra(H4)) == false
# @test mvhsalphasat(β, →(⊤, α), FiniteHeytingAlgebra(H4)) == false
# @test mvhsalphasat(β, →(⊤, β), FiniteHeytingAlgebra(H4)) == true
# @test mvhsalphasat(β, →(⊤, ⊤), FiniteHeytingAlgebra(H4)) == true

# @test mvhsalphasat(⊤, →(⊥, ⊥), FiniteHeytingAlgebra(H4)) == true
# @test mvhsalphasat(⊤, →(⊥, α), FiniteHeytingAlgebra(H4)) == true
# @test mvhsalphasat(⊤, →(⊥, β), FiniteHeytingAlgebra(H4)) == true
# @test mvhsalphasat(⊤, →(⊥, ⊤), FiniteHeytingAlgebra(H4)) == true
# @test mvhsalphasat(⊤, →(α, ⊥), FiniteHeytingAlgebra(H4)) == false
# @test mvhsalphasat(⊤, →(α, α), FiniteHeytingAlgebra(H4)) == true
# @test mvhsalphasat(⊤, →(α, β), FiniteHeytingAlgebra(H4)) == false
# @test mvhsalphasat(⊤, →(α, ⊤), FiniteHeytingAlgebra(H4)) == true
# @test mvhsalphasat(⊤, →(β, ⊥), FiniteHeytingAlgebra(H4)) == false
# @test mvhsalphasat(⊤, →(β, α), FiniteHeytingAlgebra(H4)) == false
# @test mvhsalphasat(⊤, →(β, β), FiniteHeytingAlgebra(H4)) == true
# @test mvhsalphasat(⊤, →(β, ⊤), FiniteHeytingAlgebra(H4)) == true
# @test mvhsalphasat(⊤, →(⊤, ⊥), FiniteHeytingAlgebra(H4)) == false
# @test mvhsalphasat(⊤, →(⊤, α), FiniteHeytingAlgebra(H4)) == false
# @test mvhsalphasat(⊤, →(⊤, β), FiniteHeytingAlgebra(H4)) == false
# @test mvhsalphasat(⊤, →(⊤, ⊤), FiniteHeytingAlgebra(H4)) == true

# @test mvhsalphasat(⊥, →(parseformula("p"), ⊥), FiniteHeytingAlgebra(H4)) == true
# @test mvhsalphasat(⊥, →(parseformula("p"), α), FiniteHeytingAlgebra(H4)) == true
# @test mvhsalphasat(⊥, →(parseformula("p"), β), FiniteHeytingAlgebra(H4)) == true
# @test mvhsalphasat(⊥, →(parseformula("p"), ⊤), FiniteHeytingAlgebra(H4)) == true
# @test mvhsalphasat(α, →(parseformula("p"), ⊥), FiniteHeytingAlgebra(H4)) == true
# @test mvhsalphasat(α, →(parseformula("p"), α), FiniteHeytingAlgebra(H4)) == true
# @test mvhsalphasat(α, →(parseformula("p"), β), FiniteHeytingAlgebra(H4)) == true
# @test mvhsalphasat(α, →(parseformula("p"), ⊤), FiniteHeytingAlgebra(H4)) == true
# @test mvhsalphasat(β, →(parseformula("p"), ⊥), FiniteHeytingAlgebra(H4)) == true
# @test mvhsalphasat(β, →(parseformula("p"), α), FiniteHeytingAlgebra(H4)) == true
# @test mvhsalphasat(β, →(parseformula("p"), β), FiniteHeytingAlgebra(H4)) == true
# @test mvhsalphasat(β, →(parseformula("p"), ⊤), FiniteHeytingAlgebra(H4)) == true
# @test mvhsalphasat(⊤, →(parseformula("p"), ⊥), FiniteHeytingAlgebra(H4)) == true
# @test mvhsalphasat(⊤, →(parseformula("p"), α), FiniteHeytingAlgebra(H4)) == true
# @test mvhsalphasat(⊤, →(parseformula("p"), β), FiniteHeytingAlgebra(H4)) == true
# @test mvhsalphasat(⊤, →(parseformula("p"), ⊤), FiniteHeytingAlgebra(H4)) == true

# @test mvhsalphasat(⊥, →(⊥, parseformula("p")), FiniteHeytingAlgebra(H4)) == true
# @test mvhsalphasat(⊥, →(α, parseformula("p")), FiniteHeytingAlgebra(H4)) == true
# @test mvhsalphasat(⊥, →(β, parseformula("p")), FiniteHeytingAlgebra(H4)) == true
# @test mvhsalphasat(⊥, →(⊤, parseformula("p")), FiniteHeytingAlgebra(H4)) == true
# @test mvhsalphasat(α, →(⊥, parseformula("p")), FiniteHeytingAlgebra(H4)) == true
# @test mvhsalphasat(α, →(α, parseformula("p")), FiniteHeytingAlgebra(H4)) == true
# @test mvhsalphasat(α, →(β, parseformula("p")), FiniteHeytingAlgebra(H4)) == true
# @test mvhsalphasat(α, →(⊤, parseformula("p")), FiniteHeytingAlgebra(H4)) == true
# @test mvhsalphasat(β, →(⊥, parseformula("p")), FiniteHeytingAlgebra(H4)) == true
# @test mvhsalphasat(β, →(α, parseformula("p")), FiniteHeytingAlgebra(H4)) == true
# @test mvhsalphasat(β, →(β, parseformula("p")), FiniteHeytingAlgebra(H4)) == true
# @test mvhsalphasat(β, →(⊤, parseformula("p")), FiniteHeytingAlgebra(H4)) == true
# @test mvhsalphasat(⊤, →(⊥, parseformula("p")), FiniteHeytingAlgebra(H4)) == true
# @test mvhsalphasat(⊤, →(α, parseformula("p")), FiniteHeytingAlgebra(H4)) == true
# @test mvhsalphasat(⊤, →(β, parseformula("p")), FiniteHeytingAlgebra(H4)) == true
# @test mvhsalphasat(⊤, →(⊤, parseformula("p")), FiniteHeytingAlgebra(H4)) == true

# @test mvhsalphasat(⊥, →(parseformula("p"), parseformula("p")), FiniteHeytingAlgebra(H4)) == true
# @test mvhsalphasat(α, →(parseformula("p"), parseformula("p")), FiniteHeytingAlgebra(H4)) == true
# @test mvhsalphasat(β, →(parseformula("p"), parseformula("p")), FiniteHeytingAlgebra(H4)) == true
# @test mvhsalphasat(⊤, →(parseformula("p"), parseformula("p")), FiniteHeytingAlgebra(H4)) == true

# @test mvhsalphasat(⊥, →(parseformula("p"), parseformula("q")), FiniteHeytingAlgebra(H4)) == true
# @test mvhsalphasat(α, →(parseformula("p"), parseformula("q")), FiniteHeytingAlgebra(H4)) == true
# @test mvhsalphasat(β, →(parseformula("p"), parseformula("q")), FiniteHeytingAlgebra(H4)) == true
# @test mvhsalphasat(⊤, →(parseformula("p"), parseformula("q")), FiniteHeytingAlgebra(H4)) == true

# @test mvhsalphasat(⊥, →(parseformula("q"), parseformula("p")), FiniteHeytingAlgebra(H4)) == true
# @test mvhsalphasat(α, →(parseformula("q"), parseformula("p")), FiniteHeytingAlgebra(H4)) == true
# @test mvhsalphasat(β, →(parseformula("q"), parseformula("p")), FiniteHeytingAlgebra(H4)) == true
# @test mvhsalphasat(⊤, →(parseformula("q"), parseformula("p")), FiniteHeytingAlgebra(H4)) == true
