"""
All formulas appearing in the tableau will be bounding implications, i.e.,
a → A (or A → a), where a is a propositional constant and asserting a ≤ A (resp. A ≤ a)
"""
struct SignedFormula
    sign::Bool
    boundingimplication::Union{Tuple{HeytingTruth, Formula}, Tuple{Formula, HeytingTruth}}
    
    function SignedFormula(
        sign::Bool,
        boundingimplication::Union{
            Tuple{HeytingTruth, Formula},
            Tuple{Formula, HeytingTruth}
        }
    )
        return new(sign, boundingimplication)
    end
end

sign(signedformula::SignedFormula) = signedformula.sign
boundingimplication(signedformula::SignedFormula) = signedformula.boundingimplication

function SoleLogics.height(signedformula::SignedFormula)
    formula = boundingimplication(signedformula)
    if formula isa Tuple{HeytingTruth, Formula}
        return height(formula[2]) + 1
    elseif formula isa Tuple{Formula, HeytingTruth}
        return height(formula[1]) + 1
    else
        return 1
    end
end

struct FuzzyTableau <: AbstractTableau
    signedformula::SignedFormula
    father::Base.RefValue{Set{FuzzyTableau}}
    children::Base.RefValue{Set{FuzzyTableau}}
    expanded::Base.RefValue{Bool}
    closed::Base.RefValue{Bool}

    function FuzzyTableau(
        signedformula::SignedFormula,
        father::Base.RefValue{Set{FuzzyTableau}},
        children::Base.RefValue{Set{FuzzyTableau}},
        expanded::Base.RefValue{Bool},
        closed::Base.RefValue{Bool}
    )
        return new(signedformula, father, children, expanded, closed)
    end

    function FuzzyTableau(signedformula::SignedFormula, father::FuzzyTableau)
        ft = FuzzyTableau(
            signedformula,
            Ref(Set{FuzzyTableau}([father])),
            Ref(Set{FuzzyTableau}()),
            Ref(false),
            Ref(false)
        )
        pushchildren!(father, ft)
        return ft
    end

    function FuzzyTableau(signedformula::SignedFormula)
        return FuzzyTableau(
            signedformula,
            Ref(Set{FuzzyTableau}()),
            Ref(Set{FuzzyTableau}()),
            Ref(false),
            Ref(false)
        )
    end
end

signedformula(ft::FuzzyTableau) = ft.signedformula
fatherset(ft::FuzzyTableau) = ft.father[]
father(ft::FuzzyTableau) = isempty(fatherset(ft)) ? nothing : first(fatherset(ft))
childrenset(ft::FuzzyTableau) = ft.children[]

isexpanded(ft::FuzzyTableau) = ft.expanded[]
isclosed(ft::FuzzyTableau) = ft.expanded[]

expand!(ft::FuzzyTableau) = ft.expanded[] = true
close!(ft::FuzzyTableau) = ft.closed[] = true

isroot(ft::FuzzyTableau) = isnothing(father(ft))

function findexpansionnode(ft::FuzzyTableau)
    if isexpanded(ft)
        return nothing
    elseif isroot(ft) || isexpanded(father(ft))
        return ft
    else
        findexpansionnode(father(ft))
    end
end

isleaf(ft::FuzzyTableau) = isempty(childrenset(ft)) ? true : false

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

function pushchildren!(ft::FuzzyTableau, children::FuzzyTableau...)
    push!(childrenset(ft), children...)
end

"""
    Given a FuzzyTableau containing a signed formula in the form T(b → X) or F(a → X),
    return true if there is a tableau in the form F(a → X) (resp. T(b → X)) so that a ≤ b
    in the given algebra in the same branch.
    """
function findsimilar(ft::FuzzyTableau, h::HeytingAlgebra)
    sz = signedformula(ft)
    s = sign(sz)
    z = boundingimplication(sz)

    # BooleanTruth conversions
    if z isa Tuple{Any, BooleanTruth}
        z = (z[1], HeytingTruth(z[2]))
    elseif z isa Tuple{BooleanTruth, Any}
        z = (HeytingTruth(z[1]), z[2])
    elseif z isa Tuple{BooleanTruth, BooleanTruth}
        z = (HeytingTruth(z[1]), HeytingTruth(z[2]))
    end

    if s
        # Looking for F(a→X) where a≤b
        while !isroot(ft)
            ft = father(ft)
            sy = signedformula(ft)
            y = boundingimplication(sy)

            # BooleanTruth conversions
            if y isa Tuple{Any, BooleanTruth}
                y = (y[1], HeytingTruth(y[2]))
            elseif y isa Tuple{BooleanTruth, Any}
                y = (HeytingTruth(y[1]), y[2])
            elseif y isa Tuple{BooleanTruth, BooleanTruth}
                y = (HeytingTruth(y[1]), HeytingTruth(y[2]))
            end

            if !sign(sy) && z[2] == y[2] && precedeq(h, y[1], z[1])
                return true
            end
        end
    else
        # Looking for T(b→X) where a≤b
        while !isroot(ft)
            ft = father(ft)
            sy = signedformula(ft)
            y = boundingimplication(sy)

            # BooleanTruth conversions
            if y isa Tuple{Any, BooleanTruth}
                y = (y[1], HeytingTruth(y[2]))
            elseif y isa Tuple{BooleanTruth, Any}
                y = (HeytingTruth(y[1]), y[2])
            elseif y isa Tuple{BooleanTruth, BooleanTruth}
                y = (HeytingTruth(y[1]), HeytingTruth(y[2]))
            end

            if sign(sy) && z[2] == y[2] && precedeq(h, z[1], y[1])
                return true
            end
        end
    end
    return false
end

function sat(leaves::Vector{MetricHeap}, chooseleaf::Function, h::HeytingAlgebra)
    cycle = 0
    while true
        leaf = chooseleaf(leaves, cycle)
        isnothing(leaf) && return false # all branches are closed
        en = findexpansionnode(leaf)
        isnothing(en) && return true    # found a satisfiable branch
        isclosed(en) && continue

        sz = signedformula(en)
        s = sign(sz)
        z = boundingimplication(sz)

        # BooleanTruth conversions
        if z isa Tuple{Any, BooleanTruth}
            z = (z[1], HeytingTruth(z[2]))
        elseif z isa Tuple{BooleanTruth, Any}
            z = (HeytingTruth(z[1]), z[2])
        elseif z isa Tuple{BooleanTruth, BooleanTruth}
            z = (HeytingTruth(z[1]), HeytingTruth(z[2]))
        end

        if z isa Tuple{HeytingTruth, HeytingTruth}
            # Branch Closure Conditions
            if s && !precedeq(h, z[1], z[2])
                # T(a→b) where a≰b case
                close!(en)
            elseif !s && precedeq(h, z[1], z[2]) && !isbot(z[1]) && !isbot(z[2])
                # F(a→b) where a≤b and a≠⊥ and b≠⊤ case
                close!(en)
            elseif !s && isbot(z[1])
                # F(⊥→X) case
                close!(en)
            elseif !s && istop(z[2])
                # F(X→⊤) case
                close!(en)
            elseif findsimilar(en, h)
                # T(b→X) and F(a→X) where a ≤ b case
                close!(en)
            # Base case
            else
                # No condition matched, pushing leaf back into leaves
                expand!(en)
                push!(leaves, leaf)
            end
        elseif z isa Tuple{HeytingTruth, Formula}
            # Branch Closure Conditions
            if !s && isbot(z[1])
                # F(⊥→X) case
                close!(en)
            elseif findsimilar(en, h)
                # T(b→X) and F(a→X) where a ≤ b case
                close!(en)
            # Conjunction Rules
            elseif s && token(z[2]) isa NamedConnective{:∧} && !isbot(z[1])
                # T(t→(A∧B)) case
                expand!(en)
                (a, b) = children(z[2])
                for l ∈ findleaves(en)
                    fta = FuzzyTableau(SignedFormula(true, (z[1], a)), l)
                    ftb = FuzzyTableau(SignedFormula(true, (z[1], b)), fta)
                    push!(leaves, ftb)
                end
            elseif !s && token(z[2]) isa NamedConnective{:∧} && !isbot(z[1])
                # F(t→(A∧B)) case
                expand!(en)
                (a, b) = children(z[2])
                for l ∈ findleaves(en)
                    fta = FuzzyTableau(SignedFormula(false, (z[1], a)), l)
                    push!(leaves, fta)
                    ftb = FuzzyTableau(SignedFormula(false, (z[1], b)), l)
                    push!(leaves, ftb)
                end
            # Implication Rules
            elseif !s && token(z[2]) isa NamedConnective{:→} && !isbot(z[1])
                # F(t→(A→B)) case
                expand!(en)
                (a, b) = children(z[2])
                for l ∈ findleaves(en)
                    lvs = lesservalues(h, z[1])
                    push!(lvs, z[1])
                    for ti ∈ lvs
                        isbot(ti) && continue
                        fta = FuzzyTableau(SignedFormula(true, (ti, a)), l)
                        ftb = FuzzyTableau(SignedFormula(false, (ti, b)), fta)
                        push!(leaves, ftb)
                    end                    
                end
            elseif s && token(z[2]) isa NamedConnective{:→} && !isbot(z[1])
                # T(t→(A→B)) case
                expand!(en)
                (a, b) = children(z[2])
                for l ∈ findleaves(en)
                    lvs = lesservalues(h, z[1])
                    push!(lvs, z[1])
                    if length(lvs) > 1
                        ti = last(lvs)
                        fta = FuzzyTableau(SignedFormula(false, (ti, a)), l)
                        push!(leaves, fta)
                        ftb = FuzzyTableau(SignedFormula(true, (ti, b)), l)
                        push!(leaves, ftb) 
                    end
                end
            # Atom case
            elseif z[2] isa Atom
                # a→X where X isa Atom case
                expand!(en)
                push!(leaves, leaf)
            # Reversal Rules
            elseif !s && !isbot(z[1])
                # F(a→X) case
                expand!(en)
                for l ∈ findleaves(en)
                    for ti ∈ maximalmembers(h, z[1])
                        fti = FuzzyTableau(SignedFormula(true, (z[2], ti)), l)
                        push!(leaves, fti)
                    end
                end
            elseif s && !isbot(z[1])
                # T(a→X) case
                expand!(en)
                for l ∈ findleaves(en)
                    ti = first(maximalmembers(h, z[1]))
                    fti = FuzzyTableau(SignedFormula(false, (z[2], ti)), l)
                    push!(leaves, fti)
                end
            # Base case
            else
                # No condition matched, pushing leaf back into leaves
                expand!(en)
                push!(leaves, leaf)
            end
        elseif z isa Tuple{Formula, HeytingTruth}
            # Branch Closure Conditions
            if !s && istop(z[2])
                # F(X→⊤) case
                close!(en)
            # Disjunction Rules
            elseif s && token(z[1]) isa NamedConnective{:∨} && !istop(z[2])
                # T((A∨B)→t) case
                expand!(en)
                (a, b) = children(z[1])
                for l ∈ findleaves(en)
                    fta = FuzzyTableau(SignedFormula(true, (a, z[2])), l)
                    ftb = FuzzyTableau(SignedFormula(true, (b, z[2])), fta)
                    push!(leaves, ftb)
                end
            elseif !s && token(z[1]) isa NamedConnective{:∨} && !istop(z[2])
                # F((A∨B)→t) case
                expand!(en)
                (a, b) = children(z[1])
                for l ∈ findleaves(en)
                    fta = FuzzyTableau(SignedFormula(false, (a, z[2])), l)
                    push!(leaves, fta)
                    ftb = FuzzyTableau(SignedFormula(false, (b, z[2])), l)
                    push!(leaves, ftb)
                end
            # Reversal Rules
            elseif !s && !istop(z[2])
                # F(X→a) case
                expand!(en)
                for l ∈ findleaves(en)
                    for ui ∈ minimalmembers(h, z[2])
                        fti = FuzzyTableau(SignedFormula(true, (ui, z[1])), l)
                        push!(leaves, fti)
                    end
                end
            elseif s && istop(z[2])
                # T(a→X) case
                expand!(en)
                for l ∈ findleaves(en)
                    ui = first(minimalmembers(h, z[2]))
                    fti = FuzzyTableau(SignedFormula(false, (ui, z[1])), l)
                    push!(leaves, fti)
                end
            # Base case
            else
                # No condition matched, pushing leaf back into leaves
                expand!(en)
                push!(leaves, leaf)
            end
        else
            error("Something went wrong...")
        end
        cycle += 1
    end
end

function sat(sz::SignedFormula, h::HeytingAlgebra, chooseleaf::Function, metrics::Function...)
    metricheaps = Vector{MetricHeap}()   # Heaps to be used for tableau selection
    for metric ∈ metrics
        push!(metricheaps, MetricHeap(metric))
    end
    root = FuzzyTableau(sz)
    for metricheap ∈ metricheaps
        push!(heap(metricheap), MetricHeapNode(metric(metricheap), root))
    end
    sat(metricheaps, chooseleaf, h)
end

function sat(z::Formula, h::HeytingAlgebra, chooseleaf::Function, metrics::Function...)
    return sat(SignedFormula(true, (HeytingTruth(⊤), z)), h, chooseleaf, metrics...)
end

function sat(z::Formula, h::HeytingAlgebra; rng = Random.GLOBAL_RNG)
    randombranch(tableau::FuzzyTableau) = rand(rng, Int)
    return sat(SignedFormula(true, (HeytingTruth(⊤), z)), h, roundrobin, randombranch)
end

function prove(z::Formula, h::HeytingAlgebra; rng = Random.GLOBAL_RNG)
    randombranch(tableau::FuzzyTableau) = rand(rng, Int)
    return !fuzzysat(SignedFormula(false, (HeytingTruth(⊤), z)), h, roundrobin, randombranch)
end

function alphasat(α::HeytingTruth, z::Formula, h::HeytingAlgebra; rng = Random.GLOBAL_RNG)
    randombranch(tableau::FuzzyTableau) = rand(rng, Int)
    return sat(SignedFormula(true, (α, z)), h, roundrobin, randombranch)
end

function alphasat(α::BooleanTruth, z::Formula, h::HeytingAlgebra; rng = Random.GLOBAL_RNG)
    randombranch(tableau::FuzzyTableau) = rand(rng, Int)
    return sat(SignedFormula(true, (HeytingTruth(α), z)), h, roundrobin, randombranch)
end
