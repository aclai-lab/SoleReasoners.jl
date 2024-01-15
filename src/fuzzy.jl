"""
All formulas appearing in the t will be bounding implications, i.e.,
a → A or A → a, where a is a propositional constant and asserting a ≤ A
"""
struct SignedFormula
    sign::Bool
    formula::Union{Tuple{HeytingTruth, Formula}, Tuple{Formula, HeytingTruth}}
end

sign(signedformula::SignedFormula)::Bool = signedformula.sign
formula(signedformula::SignedFormula)::Union{Tuple{HeytingTruth, Formula}, Tuple{Formula, HeytingTruth}} = signedformula.formula

struct FuzzyTableau
    signedformula::SignedFormula
    father::Base.RefValue{Set{FuzzyTableau}} # Note that this set contains at most one element
    children::Base.RefValue{Set{FuzzyTableau}}
    heytingalgebra::HeytingAlgebra
    expanded::Base.RefValue{Bool}
end

signedformula(t::FuzzyTableau) = t.signedformula
fatherset(t::FuzzyTableau)::Set{FuzzyTableau} = t.father[]
father(t::FuzzyTableau)::Union{FuzzyTableau, Nothing} = isempty(fatherset(t)) ? nothing : first(fatherset(t))
heytingalgebra(t::FuzzyTableau) = t.heytingalgebra
expanded(t::FuzzyTableau) = t.expanded[]

expand!(t::FuzzyTableau) = t.expanded[] = true

isroot(t::FuzzyTableau) = isnothing(father(t))
findroot(t::FuzzyTableau)::FuzzyTableau = isroot(t) ? t : findroot(father(t))

function findexpansionnode(t::FuzzyTableau)::Union{FuzzyTableau, Nothing}
    if expanded(t)
        return nothing
    else
        if isroot(t)
            return t
        else
            if expanded(father(t))
                return t
            else
                findexpansionnode(father(t))
            end
        end
    end
end

"""
Returns the similar signedformulas in the same branch, i.e.,
given the formula T(b→X), it looks for formulas of the type F(a->X) in the same branch,
so that they have different sign and same formula in the right-side of the implication
"""
function branchclosurecondition5(t::FuzzyTableau)
    sf = signedformula(t)
    s = sign(sf)
    f = formula(sf)
    x = f[2]
    if s
        b = f[1]
        # look for F(a→X)
        while(!isroot(t))
            t = father(t)
            sf2 = signedformula(t)
            s2 = sign(sf2)
            f2 = formula(sf2)
            a = f2[1]
            x2 = f2[2]
            if x2 == x && !s2 && precedes(heytingalgebra(t), a, b)
                return true
            else
                continue
            end
        end
    else
    end
    return false
end

function fuzzysat(t::FuzzyTableau, leaves::Set{FuzzyTableau})
    while(true)
        if isempty(leaves)
            return true
        else
            leaf = pop!(leaves)
            en = findexpansionnode(leaf)
            if isnothing(en)
                return false
            else
                expand!(en)
                sf = signedformula(en)
                x = formula(sf)
                # Branch closure conditions
                if x isa Tuple{HeytingTruth, HeytingTruth}
                    a = x[1]
                    b = x[2]
                    s = sign(sf)
                    h = heytingalgebra(t)
                    if s && !precedes(h, a, b)
                        # Close branch
                        # Create fake child and don't push it to heaps
                        pushfather!(leaf, leaf)
                        pushchildren!(leaf, leaf) # Use the node itself to not waste space
                    elseif !s && precedes(h, a, b) && a != HeytingTruth(⊥) && b != HeytingTruth(⊤)
                        # Close branch
                        # Create fake child and don't push it to heaps
                        pushfather!(leaf, leaf)
                        pushchildren!(leaf, leaf) # Use the node itself to not waste space
                    else
                        return false
                    end
                elseif x isa Tuple{HeytingTruth, Formula}
                    if !s && isbot(x[1])
                        # Close branch
                        # Create fake child and don't push it to heaps
                        pushfather!(leaf, leaf)
                        pushchildren!(leaf, leaf) # Use the node itself to not waste space
                    elseif branchclosurecondition5(leaf)
                        # Close branch
                        # Create fake child and don't push it to heaps
                        pushfather!(leaf, leaf)
                        pushchildren!(leaf, leaf) # Use the node itself to not waste space
                    end
                elseif x isa Tuple{Formula, HeytingTruth}
                    if !s && istop(x[2])
                        # Close branch
                        # Create fake child and don't push it to heaps
                        pushfather!(leaf, leaf)
                        pushchildren!(leaf, leaf) # Use the node itself to not waste space
                    end
                end
            end
        end
    end
end

function fuzzysat(x::Formula, h::HeytingAlgebra)
    t = FuzzyTableau(SignedFormula(false, (HeytingTruth(⊤), x)), Ref(Set{FuzzyTableau}()), Ref(Set{FuzzyTableau}()), h, false)
    leaves = Set{FuzzyTableau}()
    push!(leaves, t)
    fuzzysat(t, leaves)
end
