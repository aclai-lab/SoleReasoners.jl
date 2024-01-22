"""
All formulas appearing in the tableau will be bounding implications, i.e.,
a → A (or A → a), where a is a propositional constant and asserting a ≤ A (resp. A ≤ a)
"""
struct SignedFormula
    sign::Bool
    formula::Union{Tuple{HeytingTruth, Formula}, Tuple{Formula, HeytingTruth}}
end

sign(signedformula::SignedFormula) = signedformula.sign
formula(signedformula::SignedFormula) = signedformula.formula

struct FuzzyTableau
    signedformula::SignedFormula
    father::Base.RefValue{Set{FuzzyTableau}}
    children::Base.RefValue{Set{FuzzyTableau}}
    expanded::Base.RefValue{Bool}

    function FuzzyTableau(
        signedformula::SignedFormula,
        father::Base.RefValue{Set{FuzzyTableau}},
        children::Base.RefValue{Set{FuzzyTableau}},
        expanded::Base.RefValue{Bool}
    )
        return new(signedformula, father, children, expanded)
    end

    function FuzzyTableau(signedformula::SignedFormula, father::FuzzyTableau)
        ft = FuzzyTableau(
            signedformula,
            Ref(Set{FuzzyTableau}([father])),
            Ref(Set{FuzzyTableau}()),
            false)
        pushchildren!(father, ft
    )
        return ft
    end

    function FuzzyTableau(signedformula::SignedFormula)
        return FuzzyTableau(
            signedformula,
            Ref(Set{FuzzyTableau}()),
            Ref(Set{FuzzyTableau}()),
            false
        )
    end
end

signedformula(ft::FuzzyTableau) = ft.signedformula
fatherset(ft::FuzzyTableau) = ft.father[]
father(ft::FuzzyTableau) = isempty(fatherset(ft)) ? nothing : first(fatherset(ft))

isexpanded(ft::FuzzyTableau) = ft.expanded[]

expand!(ft::FuzzyTableau) = ft.expanded[] = true

isroot(ft::FuzzyTableau) = isnothing(father(ft))
findroot(ft::FuzzyTableau)::FuzzyTableau = isroot(ft) ? ft : findroot(father(ft))

function findexpansionnode(ft::FuzzyTableau)
    isexpanded(ft) && return nothing
    if isroot(ft) || isexpanded(father(ft))
        return ft
    else
        findexpansionnode(father(ft))
    end
end

function findleaves(leavesset::Set{FuzzyTableau}, ft::FuzzyTableau)
    children = childrenset(ft)
    if isempty(children)
        push!(leavesset, ft)
    else
        for child ∈ children
            findleaves(leavesset, child)
        end
    end
    return leavesset
end

function findleaves(ft::FuzzyTableau)
    findleaves(Set{FuzzyTableau}(), ft)
end

function fuzzysat(leaves::Set{FuzzyTableau}, h::HeytingAlgebra)

    function closebranch(branch::FuzzyTableau)
        for l ∈ findleaves(branch)
            expand!(l)
        end
    end


    """
    Given a FuzzyTableau containing a signed formula in the form T(b → X) or F(a → X),
    return true if there is a tableau in the form F(a → X) (resp. T(b → X)) so that a ≤ b
    in the given algebra in the same branch.
    """
    function findsimilar(ft::FuzzyTableau, h::HeytingAlgebra)
        sz = signedformula(ft)
        s = sign(sz)
        z = formula(sz)
        x = z[2]
        if s
            # T(b → X) case
            b = z[1]
            # look for F(a → X)
            while(!isroot(ft))
                ft = father(ft)
                sz2 = signedformula(ft)
                sign(sz2) && continue
                z2 = formula(sz2)
                a = z2[1]
                z2[2] != x && continue
                if precedes(h, a, b)
                    return true
                else
                    continue
                end
            end
        else
            # F(a → X) case
            a = z[1]
            # look for T(b → X)
            while(!isroot(ft))
                ft = father(ft)
                sz2 = signedformula(ft)
                !sign(sz2) && continue
                z2 = formula(sz2)
                b = z2[1]
                z2[2] != x && continue
                if precedes(h, a, b)
                    return true
                else
                    continue
                end
            end
        end
        return false
    end

    while(true)
        isempty(leaves) && return true
        leaf = pop!(leaves)
        en = findexpansionnode(leaf)
        if isnothing(en) && continue
        expand!(en)
        sz = signedformula(en)
        s = sign(sz)
        z = formula(sz)
        if z isa Tuple{HeytingTruth, HeytingTruth} # a → b
            a = z[1]
            b = z[2]
            if s && !precedes(h, a, b)
                # T(a → b) where a ≰ b case
                closebranch(en)
            elseif !s precedes(h, a, b) && a != HeytingTruth(⊥) && b != HeytingTruth(⊤)
                # T(b → X) and F(a → X) where a ≤ b case
                closebranch(en)
            else
                continue
            end
        elseif z isa Tuple{HeytingTruth, Formula} # a → X
            a = z[1]
            x = z[2]
            if findsimilar(en, h)
                closebranch(en)
            elseif s
                if isbot(a)
                    # T(⊥ → X) case
                    # ...
                elseif token(x) isa NamedConnective{:∧}
                    # T(t → (A ∧ B)) case
                    for l ∈ findleaves(en)
                        ftᵢ = l
                        for c ∈ children(x)
                            ftᵢ = FuzzyTableau(SignedFormula(true, (a, c)), ftᵢ)
                        end
                        push!(leaves, ftᵢ)
                    end
                else
                    # T(a → X) case
                    tᵢ = first(maximalmembers(h, a))
                    for l ∈ findleaves(en)
                        ftᵢ = FuzzyTableau(SignedFormula(false, (x, tᵢ)), l)
                        push!(leaves, ftᵢ)
                    end
                end
            else
                if isbot(a)
                    # F(⊥ → X) case
                    closebranch(leaf)
                elseif token(x) isa NamedConnective{:∧}
                    # F(t → (A ∧ B)) case
                    for l ∈ findleaves(en)
                        for c ∈ children(x)
                            ftᵢ = FuzzyTableau(SignedFormula(true, (a, c)), l)
                            push!(leaves, ftᵢ)
                        end
                    end
                else
                    # F(a → X) case
                    for l ∈ findleaves(en)
                        for tᵢ ∈ maximalmembers(h, a)
                            ftᵢ = FuzzyTableau(SignedFormula(true, (x, tᵢ)), l)
                            push!(leaves, ftᵢ)
                        end
                    end
                end
            end
        elseif z isa Tuple{Formula, HeytingTruth} # x → a
            x = z[1]
            a = z[2]
            if s
                if istop(a)
                    # T(X → ⊤) case
                    # ...
                else
                    # T(X → a) case
                    uᵢ = first(minimalmembers(h, a))
                    for l ∈ findleaves(en)
                        ftᵢ = FuzzyTableau(SignedFormula(false, (uᵢ, x)), l)
                        push!(leaves, ftᵢ)
                    end
                end
            else
                if istop(a)
                    # F(⊤ → X) case
                    closebranch(leaf)
                else
                    # F(X → a) case
                    for l ∈ findleaves(en)
                        for uᵢ ∈ minimalmembers(h, a)
                            ftᵢ = FuzzyTableau(SignedFormula(true, (uᵢ, x)), l)
                            push!(leaves, ftᵢ)
                        end
                    end
                end
            end
        end
    end
end

function fuzzysat(z::Formula, h::HeytingAlgebra)
    ft = FuzzyTableau(SignedFormula(false, (HeytingTruth(⊤), z)))
    leaves = Set{FuzzyTableau}()
    push!(leaves, ft)
    fuzzysat(leaves, h)
end
