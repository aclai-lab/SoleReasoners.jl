using SoleReasoners
using SoleLogics: Atom, ∧, ∨, →, ¬, ⊤, box, LTLFP_F
using SoleLogics.ManyValuedLogics: booleanalgebra, G3, α

p, q = Atom.(["p", "q"])

# Classical propositional tableau.
@assert sat(∧(p, ¬p)) == false
@assert sat(∨(p, q), roundrobin!, distancefromroot) == true

# The same many-valued formula through all four supported tableau families.
for tableau in (MVLTLFPTableau, MVCLTableau, MVHSTableau, MVLRCC8Tableau)
    @assert alphasat(tableau, ⊤, ∧(p, q), booleanalgebra) == true
end

# A non-Boolean finite algebra and validity.
@assert alphaval(MVLTLFPTableau, α, →(p, p), G3) == true

# A temporal operator supplied by SoleLogics; timeout bounds frame search.
@assert alphasat(MVLTLFPTableau, ⊤, box(LTLFP_F)(p), booleanalgebra;
                  timeout=10) == true

println("SoleReasoners playground completed")
