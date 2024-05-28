using SoleLogics
using SoleLogics.ManyValuedLogics
using SoleReasoners
using Test

using SoleReasoners: Point, AFSLOS, checkafslos, mvhsalphasat

using SoleLogics.ManyValuedLogics: α, β, H4

u, v = Point.(["u", "v"])
afslos1 = AFSLOS(
    [u, v],
    FiniteHeytingAlgebra(H4),
    Dict(
        (u,u) => ⊥, (u,v) => α,
        (v,u) => β, (v,v) => ⊥
    ),
    Dict(
        (u,u) => ⊤, (u,v) => ⊥,
        (v,u) => ⊥, (v,v) => ⊤
    )
)

let err = nothing
    try
        checkafslos(afslos1)
    catch err
    end

    @test sprint(showerror, err)  == "(D,<,=) is not a AFSLOS (5)"
end

using SoleLogics.ManyValuedLogics: G3

w = Point("w")
afslos2 = AFSLOS(
    [u, v, w],
    FiniteHeytingAlgebra(G3),
    Dict(
        (u,u) => ⊥, (u,v) => ⊤, (u,w) => α,
        (v,u) => ⊥, (v,v) => ⊥, (v,w) => ⊤,
        (w,u) => ⊥, (w,v) => ⊥, (w,w) => ⊥
    ),
    Dict(
        (u,u) => ⊤, (u,v) => ⊥, (u,w) => ⊥,
        (v,u) => ⊥, (v,v) => ⊤, (v,w) => ⊥,
        (w,u) => ⊥, (w,v) => ⊥, (w,w) => ⊤
    )
)

let err = nothing
    try
        checkafslos(afslos2)
    catch err
    end

    @test sprint(showerror, err)  == "(D,<,=) is not a AFSLOS (4)"
end

p, q = Atom.(["p", "q"])
diamondA = diamond(IA_A)
boxA = box(IA_A)
mvhsalphasat(⊤, ∧(diamondA(p), boxA(→(p, ⊥))), FiniteHeytingAlgebra(G3), verbose=true)
