############################################################################################
# This was an attempt to implement the Many-Valued Modal Tableau proposed by Melvin        #
# Fitting in his seminal work in 1995. It has not been tested thoughly.                    #
# Also, keep in mind that this work is only  thought for automated theorem proving on      #
# many-valued logics representable with an Heyting algebra, and could not work on          #
# sat/alphasat and using other many-valued logics (e.g, FLew).                             #
# For the same reason, oldrule default to true.                                            #
############################################################################################

function manyvaluedmodalsat(
    metricheaps::Vector{MetricHeap},
    choosenode::Function,
    h::FiniteHeytingAlgebra{T,D};
    oldrule::Bool=true,
    verbose::Bool=false,
    timeout::Union{Nothing,Int}=nothing,
    kwargs...
) where {
    T<:Truth,
    D<:AbstractVector{T}
}
    cycle = 1
    t0 = time_ns()
    while true

        if cycle%1e3==0
            cleanheaps!(metricheaps)
        end

        # if timeout, return false with a warning
        if !isnothing(timeout) && (time_ns()-t0)/1e9 > timeout
            verbose && println("Timeout")
            return nothing
        end

        # if using too much memory, try to free memory calling full GC sweep
        if cycle%10==0 && getfreemem() < gettotmem()*5e-2
            verbose && println("Calling Garbage Collector")
            GC.gc()
        end
        # if using too much memory, kill execution to avoid crashes
        if cycle%10==0 && getfreemem() < gettotmem()*5e-2
            verbose && println("Too much memory being used, exiting")
            return nothing
        end

        node = choosenode(metricheaps, cycle)
        isnothing(node) && return false # all branches are closed
        if isexpanded(node) # found a satisfiable branch
            verbose && println(node) # print satisfiable branch
            return true
        end
        en = findexpansionnode(node)
        expand!(en)

        sz = en.signedformula
        if !isa(sz, SignedFormula{T})
            sz = convert(SignedFormula{T}, sz)::SignedFormula{T}
        end
        s = sz.sign
        z = sz.boundingimplication

        verbose && println(string(s) * "\t" * string(z))

        if z isa Tuple{Truth, Truth}
            # Branch Closure Conditions
            if s && !precedeq(h, z[1], z[2])
                # T(a→b) where a≰b case
                close!(en)
            elseif !s && precedeq(h, z[1], z[2]) && !isbot(z[1]) && !istop(z[2])
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
                # No condition matched, pushing node back into metricheaps
                push!(metricheaps, node)
            end
        elseif z isa Tuple{T, Formula}
            # Branch Closure Conditions
            if !s && isbot(z[1])
                # F(⊥→X) case
                close!(en)
            elseif findsimilar(en, h)
                # T(b→X) and F(a→X) where a ≤ b case
                close!(en)
            # Weak conjunction Rules
            elseif s && token(z[2]) isa NamedConnective{:∧} && !isbot(z[1])
                # T(t→(A∧B)) case
                (a, b) = children(z[2])
                for l ∈ findleaves(en)
                    fta = ManyValuedTableau(SignedFormula(true, (z[1], a)), l)
                    push!(metricheaps, fta)
                    ftb = ManyValuedTableau(SignedFormula(true, (z[1], b)), fta)
                    push!(metricheaps, ftb)
                end
            elseif !s && token(z[2]) isa NamedConnective{:∧} && !isbot(z[1])
                # F(t→(A∧B)) case
                (a, b) = children(z[2])
                for l ∈ findleaves(en)
                    fta = ManyValuedTableau(SignedFormula(false, (z[1], a)), l)
                    push!(metricheaps, fta)
                    ftb = ManyValuedTableau(SignedFormula(false, (z[1], b)), l)
                    push!(metricheaps, ftb)
                end
            # Implication rules
            elseif !s && token(z[2]) isa NamedConnective{:→} && !isbot(z[1])
                # F(t→(A→B)) case
                (a, b) = children(z[2])
                lvs = lesservalues(h, z[1])
                push!(lvs, z[1])
                for l ∈ findleaves(en)
                    newnodes = false
                    for ti ∈ lvs
                        if !isbot(ti)
                            newnodes = true
                            fta = ManyValuedTableau(SignedFormula(true, (ti, a)), l)
                            push!(metricheaps, fta)
                            ftb = ManyValuedTableau(SignedFormula(false, (ti, b)), fta)
                            push!(metricheaps, ftb)
                        end
                    end
                    !newnodes && l == node && push!(metricheaps, node)   
                end
            elseif s && token(z[2]) isa NamedConnective{:→} && !isbot(z[1])
                if oldrule
                    # (OLD) T(t→(A→B)) case
                    (a, b) = children(z[2])
                    lvs = lesservalues(h, z[1])
                    push!(lvs, z[1])
                    newnodes = false
                    for ti in lvs
                        if !isbot(ti)
                            for l ∈ findleaves(en)
                                if l == node
                                    newnodes = true
                                end
                                fta = ManyValuedTableau(SignedFormula(false, (ti, a)), l)
                                push!(metricheaps, fta)
                                ftb = ManyValuedTableau(SignedFormula(true, (ti, b)), l)
                                push!(metricheaps, ftb)
                            end
                        end
                        !newnodes && push!(metricheaps, node)
                    end
                else
                    # (NEW) T(t→(A→B)) case
                    (a, b) = children(z[2])
                    # Search for support tuples
                    pairs = Set{NTuple{2,T}}()
                    for ti ∈ getdomain(h)
                        for si ∈ getdomain(h)
                            if precedeq(h, z[1], h.implication(ti, si))
                                push!(pairs, (ti, si))
                            end
                        end
                    end
                    for p in pairs
                        for q in pairs
                            if precedeq(h, p[1], q[1]) && precedeq(h, q[2], p[2]) && p != q
                                delete!(pairs, p)
                            end
                        end
                    end
                    for l ∈ findleaves(en)
                        newnodes = false
                        for pair in pairs
                            newnodes = true
                            sy = SignedFormula(true, (a, pair[1]))
                            if !findformula(l, sy)
                                fta = ManyValuedTableau(sy, l)
                                push!(metricheaps, fta)
                                sy = SignedFormula(true, (pair[2], b))
                                if !findformula(fta, sy)
                                    ftb = ManyValuedTableau(sy, fta)
                                    push!(metricheaps, ftb)
                                end
                            else
                                sy = SignedFormula(true, (pair[2], b))
                                if !findformula(l, sy)
                                    newnodes = true
                                    ftb = ManyValuedTableau(sy, l)
                                    push!(metricheaps, ftb)
                                else  # Here there should be a branch and I need to keep track of it
                                    sy = SignedFormula(true, (⊤, ⊤))    # Fake node (always true)
                                    fti = ManyValuedTableau(sy, l)
                                    push!(metricheaps, fti)
                                end
                            end
                        end
                        !newnodes && l == node && push!(metricheaps, node)
                    end
                end
            # Modal Branch Replacement Rules
            elseif token(z[2]) isa NamedConnective{:◊}
                if s && !isbot(z[1])
                    # T(a→◊X) case (reversal rule)
                    for l ∈ findleaves(en)
                        newnodes = false
                        fti = l
                        for ti in maximalmembers(h, z[1])
                            newnodes = true
                            sy = SignedFormula(false, (z[2], ti))
                            fti = ManyValuedTableau(sy, fti)
                            push!(metricheaps, fti)
                        end
                        !newnodes && l == node && push!(metricheaps, node)
                    end
                elseif !s && !isbot(z[1])
                    # F(a→◊X) case (reversal rule)
                    for l ∈ findleaves(en)
                        newnodes = false
                        for ti ∈ maximalmembers(h, z[1])
                            newnodes = true
                            sy = SignedFormula(true, (z[2], ti))
                            fti = ManyValuedTableau(sy, l)
                            push!(metricheaps, fti)
                        end
                        !newnodes && l == node && push!(metricheaps, node)
                    end
                end
            elseif token(z[2]) isa NamedConnective{:□}
                if s
                    # T(a→□X)
                    # Check if T(□X→a), T(a→◊X), F(a→□X), F(◊X→a) is in the path
                    found = false
                    for l in findleaves(en)
                        slider = l
                        slider.expanded = false
                        while !isexpanded(slider)
                            sy = slider.signedformula
                            y = sy.boundingimplication
                            if (
                                sy.sign &&
                                (
                                    (
                                        y isa Tuple{Formula, T} &&
                                        token(y[1]) isa NamedConnective{:□}
                                    ) || (
                                        y isa Tuple{T, Formula} &&
                                        token(y[2]) isa NamedConnective{:◊}
                                    )
                                )
                            ) || (
                                !sy.sign &&
                                (
                                    (
                                        y isa Tuple{Formula, T} &&
                                        token(y[1]) isa NamedConnective{:◊}
                                    ) || (
                                        y isa Tuple{T, Formula} &&
                                        token(y[2]) isa NamedConnective{:□}
                                    )
                                )
                            )
                                found = true
                                break 
                            end
                            slider = slider.father
                        end
                        found && break
                    end
                    if found
                        for l in findleaves(en)
                            push!(metricheaps, ManyValuedTableau(sz, l)) # It will be useful
                        end
                    else
                        push!(metricheaps, node) # Formula is no longer useful
                    end
                else
                    # F(a→□X)
                    # Check that everything propositional has been solved
                    # and there are no more F(□X→a) and F(a→◊X) to expand
                    postpone = false
                    for l ∈ findleaves(en)
                        slider = l
                        slider.expanded = false
                        while !isexpanded(slider)
                            sy = slider.signedformula
                            y = sy.boundingimplication
                            if y isa Tuple{Formula, T}
                                if (
                                    token(y[1]) ∉ [□, ◊]
                                ) || (
                                    !sy.sign && token(y[1]) isa NamedConnective{:□}                                    
                                )
                                    postpone = true
                                    break
                                end
                            elseif y isa Tuple{T, Formula}
                                if (
                                    token(y[2]) ∉ [□, ◊]
                                ) || (
                                    !sy.sign && token(y[2]) isa NamedConnective{:◊}
                                )
                                    postpone = true
                                    break
                                end
                            elseif sy.boundingimplication isa Tuple{T, T}
                                postpone = true
                                break
                            else
                                error("Unexpected error")
                            end
                            slider = slider.father
                        end 
                        if postpone
                            break
                        end
                    end
                    if postpone
                        for l ∈ findleaves(en)
                            push!(metricheaps, ManyValuedTableau(sz, l))
                        end
                    else
                        oldleaves = findleaves(en)
                        isempty(oldleaves) && push!(metricheaps, node)
                        # evaluate S# for each leaf
                        for l in findleaves(en)
                            newnodes = false
                            for t in getdomain(h)
                                newnodes = true
                                if !isbot(h.meet(z[1], t))
                                    slider = l
                                    newleaf = l
                                    slider.expanded = false
                                    while !isexpanded(slider)
                                        sy = slider.signedformula
                                        y = sy.boundingimplication
                                        # Possible cases: T(a→□X), T(◊X→a), F(a→□X), F(◊X→a)
                                        if sy.sign
                                            if token(y[2]) isa NamedConnective{:□}
                                                if !isbot(h.meet(y[1],t))
                                                    # T(a→□X)
                                                    newleaf = ManyValuedTableau(
                                                        SignedFormula(
                                                            true,
                                                            (
                                                                h.meet(y[1], t),
                                                                y[2].children[1]
                                                            )
                                                        ),
                                                        newleaf
                                                    )
                                                    push!(metricheaps, newleaf)
                                                end
                                            elseif token(y[1]) isa NamedConnective{:◊}
                                                if !istop(h.implication(t, y[2]))
                                                    # T(◊X→a)
                                                    newleaf = ManyValuedTableau(
                                                        SignedFormula(
                                                            true,
                                                            (
                                                                y[1].children[1],
                                                                h.implication(t, y[2])
                                                            )
                                                        ),
                                                        newleaf
                                                    )
                                                    push!(metricheaps, newleaf)
                                                end
                                            else
                                                error("Unexpected error")
                                            end
                                        else
                                            # Other F(a→□X) and F(◊X→a) are discarded
                                            # (loss of information)
                                            if token(y[2]) isa NamedConnective{:□}
                                                # F(a→□X)
                                                continue
                                            elseif token(y[1]) isa NamedConnective{:◊}
                                                # F(◊X→a)
                                                continue
                                            else
                                                error("Unexpected error")
                                            end
                                        end
                                        slider = slider.father
                                    end
                                    newleaf = ManyValuedTableau(
                                        SignedFormula(
                                            false,
                                            (h.meet(z[1], t), z[2].children[1])
                                        ),
                                        newleaf
                                    )
                                    push!(metricheaps, newleaf)
                                end
                            end
                            !newnodes && l == node && push!(metricheaps, node)
                        end
                        # Mark every node from each old above (of the branch) as expanded
                        for l in oldleaves
                            slider = l
                            slider.expanded = false
                            while !isexpanded(slider)
                                expand!(slider)
                                slider = slider.father
                            end
                        end
                    end
                end
            # Reversal Rules
            elseif !s && !isbot(z[1])
                # F(a→X) case
                for l ∈ findleaves(en)
                    newnodes = false
                    for ti ∈ maximalmembers(h, z[1])
                        newnodes = true
                        sy = SignedFormula(true, (z[2], ti))
                        if !findformula(l, sy)
                            newnodes = true
                            fti = ManyValuedTableau(sy, l)
                            push!(metricheaps, fti)
                        else  # Here there should be a branch and I need to keep track of it
                            sy = SignedFormula(true, (⊤, ⊤))    # Fake node (always true)
                            fti = ManyValuedTableau(sy, l)
                            push!(metricheaps, fti)
                        end
                    end
                    !newnodes && l == node && push!(metricheaps, node)
                end
            elseif s && !isbot(z[1])
                # T(a→X) case
                for l ∈ findleaves(en)
                    newnodes = false
                    fti = l
                    for ti in maximalmembers(h, z[1])
                        sy = SignedFormula(false, (z[2], ti))
                        if !findformula(fti, sy)
                            newnodes = true
                            fti = ManyValuedTableau(sy, fti)
                            push!(metricheaps, fti)
                        end
                    end
                    !newnodes && l == node && push!(metricheaps, node)
                end
            # Error
            elseif !isa(z[2], Atom) && token(z[2]) ∉ [∧, ∨, →, □, ◊]
                error("Unrecognized operator $(token(z[2])).")
            # Base case
            else
                # No condition matched, pushing node back into metricheaps
                push!(metricheaps, node)
            end
        elseif z isa Tuple{Formula, T}
            # Branch Closure Conditions
            if !s && istop(z[2])
                # F(X→⊤) case
                close!(en)
            # Weak disjunction Rules
            elseif s && token(z[1]) isa NamedConnective{:∨} && !istop(z[2])
                # T((A∨B)→t) case
                (a, b) = children(z[1])
                for l ∈ findleaves(en)
                    fta = ManyValuedTableau(SignedFormula(true, (a, z[2])), l)
                    push!(metricheaps, fta)
                    ftb = ManyValuedTableau(SignedFormula(true, (b, z[2])), fta)
                    push!(metricheaps, ftb)
                end
            elseif !s && token(z[1]) isa NamedConnective{:∨} && !istop(z[2])
                # F((A∨B)→t) case
                (a, b) = children(z[1])
                for l ∈ findleaves(en)
                    fta = ManyValuedTableau(SignedFormula(false, (a, z[2])), l)
                    push!(metricheaps, fta)
                    ftb = ManyValuedTableau(SignedFormula(false, (b, z[2])), l)
                    push!(metricheaps, ftb)
                end
            # Modal Branch Replacement Rules 
            elseif token(z[1]) isa NamedConnective{:□}
                if s && !istop(z[2])
                    # T(□X→a) case (reversal rule)
                    for l ∈ findleaves(en)
                        newnodes = false
                        fui = l
                        for ui in minimalmembers(h, z[2])
                            newnodes = true
                            sy = SignedFormula(false, (ui, z[1]))
                            fui = ManyValuedTableau(sy, fui)
                            push!(metricheaps, fui)
                        end
                        !newnodes && l == node && push!(metricheaps, node)
                    end
                elseif !s && !istop(z[2])
                    # F(□X→a) case (reversal rule)
                    for l ∈ findleaves(en)
                        mm = minimalmembers(h, z[2])
                        newnodes = false
                        for ui ∈ mm
                            newnodes = true
                            sy = SignedFormula(true, (ui, z[1]))
                            fui = ManyValuedTableau(sy, l)
                            push!(metricheaps, fui)
                        end
                        !newnodes && l == node && push!(metricheaps, node)
                    end
                end                
            elseif token(z[1]) isa NamedConnective{:◊}
                if s
                    # T(◊X→a)
                    # Check if T(□X→a), T(a→◊X), F(a→□X), F(◊X→a) is in the path
                    found = false
                    for l in findleaves(en)
                        slider = l
                        slider.expanded = false
                        while !isexpanded(slider)
                            sy = slider.signedformula
                            y = sy.boundingimplication
                            if (
                                sy.sign &&
                                (
                                    (
                                        y isa Tuple{Formula, T} &&
                                        token(y[1]) isa NamedConnective{:□}
                                    ) || (
                                        y isa Tuple{T, Formula} &&
                                        token(y[2]) isa NamedConnective{:◊}
                                    )
                                )
                            ) || (
                                !sy.sign &&
                                (
                                    (
                                        y isa Tuple{Formula, T} &&
                                        token(y[1]) isa NamedConnective{:◊}
                                    ) || (
                                        y isa Tuple{T, Formula} &&
                                        token(y[2]) isa NamedConnective{:□}
                                    )
                                )
                            )
                               found = true
                               break 
                            end
                            slider = slider.father
                        end
                        found && break
                    end
                    if found
                        for l in findleaves(en)
                            push!(metricheaps, ManyValuedTableau(sz, l)) # It will be useful
                        end
                    else
                        push!(metricheaps, node) # Formula is no longer useful
                    end
                else
                    # F(◊X→a)
                    # Check that everything propositional has been solved
                    # and there are no more F(□X→a) and F(a→◊X) to expand
                    postpone = false
                    for l ∈ findleaves(en)
                        slider = l
                        slider.expanded = false
                        while !isexpanded(slider)
                            sy = slider.signedformula
                            y = sy.boundingimplication
                            if y isa Tuple{Formula, T}
                                if (
                                    token(y[1]) ∉ [□, ◊]
                                 ) || (
                                    !sy.sign && token(y[1]) isa NamedConnective{:□}                                    
                                 )
                                    postpone = true
                                    break
                                end
                            elseif y isa Tuple{T, Formula}
                                if (
                                    token(y[2]) ∉ [□, ◊]
                                ) || (
                                    !sy.sign && token(y[2]) isa NamedConnective{:◊}
                                )
                                    postpone = true
                                    break
                                end
                            elseif sy.boundingimplication isa Tuple{T, T}
                                postpone = true
                                break
                            else
                                error("Unexpected error")
                            end
                            slider = slider.father
                        end 
                        if postpone
                            break
                        end
                    end
                    if postpone
                        for l ∈ findleaves(en)
                            push!(metricheaps, ManyValuedTableau(sz, l))
                        end
                    else
                        oldleaves = findleaves(en)
                        isempty(oldleaves) && push!(metricheaps, node)
                        # evaluate S# for each leaf
                        for l in findleaves(en)
                            newnodes = false
                            for t in getdomain(h)
                                newnodes = true
                                if !istop(h.implication(t, z[2]))
                                    slider = l
                                    newleaf = l
                                    slider.expanded = false
                                    while !isexpanded(slider)
                                        sy = slider.signedformula
                                        y = sy.boundingimplication
                                        # Possible cases: T(a→□X), T(◊X→a), F(a→□X), F(◊X→a)
                                        if sy.sign
                                            if token(y[2]) isa NamedConnective{:□}
                                                if !isbot(h.meet(y[1],t))
                                                    # T(a→□X)
                                                    newleaf = ManyValuedTableau(
                                                        SignedFormula(
                                                            true,
                                                            (
                                                                h.meet(y[1], t),
                                                                y[2].children[1]
                                                            )
                                                        ),
                                                        newleaf
                                                    )
                                                    push!(metricheaps, newleaf)
                                                end
                                            elseif token(y[1]) isa NamedConnective{:◊}
                                                if !istop(h.implication(t, y[2]))
                                                    # T(◊X→a)
                                                    newleaf = ManyValuedTableau(
                                                        SignedFormula(
                                                            true,
                                                            (
                                                                y[1].children[1],
                                                                h.implication(t, y[2])
                                                            )
                                                        ),
                                                        newleaf
                                                    )
                                                    push!(metricheaps, newleaf)
                                                end
                                            else
                                                error("Unexpected error")
                                            end
                                        else
                                            # Other F(a→□X) and F(◊X→a) are discarded
                                            # (loss of information)
                                            if token(y[2]) isa NamedConnective{:□}
                                                # F(a→□X)
                                                continue
                                            elseif token(y[1]) isa NamedConnective{:◊}
                                                # F(◊X→a)
                                                continue
                                            else
                                                error("Unexpected error")
                                            end
                                        end
                                        slider = slider.father
                                    end
                                    newleaf = ManyValuedTableau(
                                        SignedFormula(
                                            false,
                                            (z[1].children[1], h.implication(t, z[2]))
                                        ),
                                        newleaf
                                    )
                                    push!(metricheaps, newleaf)
                                end
                            end
                            !newnodes && l == node && push!(metricheaps, node)
                        end
                        # Mark every node from each old above (of the branch) as expanded
                        for l in oldleaves
                            slider = l
                            slider.expanded = false
                            while !isexpanded(slider)
                                expand!(slider)
                                slider = slider.father
                            end
                        end
                    end
                end
            # Reversal Rules
            elseif !s && !istop(z[2])
                # F(X→a) case
                for l ∈ findleaves(en)
                    newnodes = false
                    for ui ∈ minimalmembers(h, z[2])
                        newnodes = true
                        sy = SignedFormula(true, (ui, z[1]))
                        if !findformula(l, sy)
                            fui = ManyValuedTableau(sy, l)
                            push!(metricheaps, fui)
                        else  # Here there should be a branch and I need to keep track of it
                            sy = SignedFormula(true, (⊤, ⊤))    # Fake node (always true)
                            fti = ManyValuedTableau(sy, l)
                            push!(metricheaps, fti)
                        end
                    end
                    !newnodes && l == node && push!(metricheaps, node)
                end
            elseif s && !istop(z[2])
                # T(X→A) case
                for l ∈ findleaves(en)
                    newnodes = false
                    fui = l
                    for ui in minimalmembers(h, z[2])
                        sy = SignedFormula(false, (ui, z[1]))
                        if !findformula(fui, sy)
                            newnodes = true
                            fui = ManyValuedTableau(sy, fui)
                            push!(metricheaps, fui)
                        end
                    end
                    !newnodes && l == node && push!(metricheaps, node)
                end
            # Error
            elseif !isa(z[1], Atom) && token(z[1]) ∉ [∧, ∨, →, □, ◊]
                error("Unrecognized operator $(token(z[1])).")
            # Base case
            else
                # No condition matched, pushing node back into metricheaps
                push!(metricheaps, node)
            end
        else
            error("Something went wrong with tuple $(z) of type $(typeof(z))")
        end
        cycle += 1
    end
end

"""
    manyvaluedmodalsat(
        α::T1,
        z::Formula,
        a::A;
        rng = Random.GLOBAL_RNG,
        verbose::Bool=false,
        timeout::Union{Nothing,Int}=nothing,
        kwargs...
    )

Given a formula, return true if it is α-valid, i.e., there is not an interpretation that
does not satisfy the formula, nothing in case of timeout or out-of-memory error, false
otherwise.
"""
function manyvaluedmodalsat(
    sz::SignedFormula{T1},
    h::A,
    choosenode::Function,
    metrics::Function...;
    verbose::Bool=false,
    timeout::Union{Nothing,Int}=nothing,
    kwargs...
) where {
    T<:Truth,
    D<:AbstractVector{T},
    A<:FiniteAlgebra{T,D},
    T1<:Truth
}
    if !isa(sz, SignedFormula{T}) sz = convert(SignedFormula{T}, sz)::SignedFormula{T} end
    metricheaps = Vector{MetricHeap}()   # Heaps to be used for tableau selection
    for metric ∈ metrics
        push!(metricheaps, MetricHeap(metric))
    end
    root = ManyValuedTableau(sz)
    for metricheap ∈ metricheaps
        push!(heap(metricheap), MetricHeapNode(metric(metricheap), root))
    end
    manyvaluedmodalsat(metricheaps, choosenode, h; verbose, timeout, kwargs...)
end

function manyvaluedmodalsat(
    z::Formula,
    h::A,
    choosenode::Function,
    metrics::Function...;
    verbose::Bool=false,
    timeout::Union{Nothing,Int}=nothing,
    kwargs...
) where {
    T<:Truth,
    D<:AbstractVector{T},
    A<:FiniteAlgebra{T,D}
}
    return manyvaluedmodalsat(SignedFormula(true, (⊤, z)), h, choosenode, metrics...; verbose, timeout, kwargs...)
end

"""
    manyvaluedmodalsat(
        z::Formula,
        h::A;
        rng = Random.GLOBAL_RNG,
        verbose::Bool=false,
        timeout::Union{Nothing,Int}=nothing,
        kwargs...
    ) where {
        T<:Truth,
        D<:AbstractVector{T},
        A<:FiniteAlgebra{T,D}
    }

Given a formula, return true if an interpretation that satisfies the formula exists, false
otherwise.
"""
function manyvaluedmodalsat(
    z::Formula,
    h::A;
    rng = Random.GLOBAL_RNG,
    verbose::Bool=false,
    timeout::Union{Nothing,Int}=nothing,
    kwargs...
) where {
    T<:Truth,
    D<:AbstractVector{T},
    A<:FiniteAlgebra{T,D}
}
    randombranch(_::ManyValuedTableau{T}) where {T<:Truth} = rand(rng, Int)
    return manyvaluedmodalsat(SignedFormula(true, (⊤, z)), h, roundrobin, randombranch; verbose, timeout, kwargs...)
end
"""
    manyvaluedmodalprove(
        z::Formula,
        h::A;
        rng = Random.GLOBAL_RNG,
        verbose::Bool=false,
        timeout::Union{Nothing,Int}=nothing,
        kwargs...
    ) where {
        T<:Truth,
        D<:AbstractVector{T},
        A<:FiniteAlgebra{T,D}
    }

Given a formula, return true if it is valid, i.e., there is not an interpretation that does
not satisfy the formula, false otherwise.
"""
function manyvaluedmodalprove(
    z::Formula,
    h::A;
    rng = Random.GLOBAL_RNG,
    verbose::Bool=false,
    timeout::Union{Nothing,Int}=nothing,
    kwargs...
) where {
    T<:Truth,
    D<:AbstractVector{T},
    A<:FiniteAlgebra{T,D}
}
    randombranch(_::ManyValuedTableau) = rand(rng, Int)
    r = manyvaluedmodalsat(SignedFormula(false, (⊤, z)), h, roundrobin, randombranch; verbose, timeout, kwargs...)
    if isnothing(r)
        return r
    else
        return !r
    end
end

"""
    manyvaluedmodalalphasat(
        α::T1,
        z::Formula,
        a::A;
        rng = Random.GLOBAL_RNG,
        verbose::Bool=false,
        timeout::Union{Nothing,Int}=nothing,
        kwargs...
    ) where {
        T<:Truth,
        D<:AbstractVector{T},
        A<:FiniteAlgebra{T,D},
        T1<:Truth
    }

Given a formula, return true if it is α-satisfiable, i.e., there is an interpretation such
that the formula assumes value of at least α, nothing in case of timeout or out-of-memory
error, false otherwise.
"""
function manyvaluedmodalalphasat(
    α::T1,
    z::Formula,
    a::A;
    rng = Random.GLOBAL_RNG,
    verbose::Bool=false,
    timeout::Union{Nothing,Int}=nothing,
    kwargs...
) where {
    T<:Truth,
    D<:AbstractVector{T},
    A<:FiniteAlgebra{T,D},
    T1<:Truth
}
    if verbose
        println("Solving manyvaluedmodalalphasat for: " * syntaxstring(α) * " ⪯ " * syntaxstring(z))
        println("Height: " * string(height(z)))
        println("Tokens: " * string(ntokens(z)))
        println()
    end
    randombranch(_::ManyValuedTableau) = rand(rng, Int)
    return manyvaluedmodalsat(SignedFormula(true, (α, z)), a, roundrobin, randombranch; verbose, timeout, kwargs...)
end

"""
    manyvaluedmodalalphaprove(
        α::T1,
        z::Formula,
        a::A;
        rng = Random.GLOBAL_RNG,
        verbose::Bool=false,
        timeout::Union{Nothing,Int}=nothing,
        kwargs...
    ) where {
        T<:Truth,
        D<:AbstractVector{T},
        A<:FiniteAlgebra{T,D},
        T1<:Truth
    }

Given a formula, return true if it is α-valid, i.e., there is not an interpretation such
that the formula does not assume value of at least α, nothing in case of timeout or
out-of-memory error, false otherwise.
"""
function manyvaluedmodalalphaprove(
    α::T1,
    z::Formula,
    a::A;
    rng = Random.GLOBAL_RNG,
    verbose::Bool=false,
    timeout::Union{Nothing,Int}=nothing,
    kwargs...
) where {
    T<:Truth,
    D<:AbstractVector{T},
    A<:FiniteAlgebra{T,D},
    T1<:Truth
}
    if verbose
        println("Solving manyvaluedmodalalphaprove for: " * syntaxstring(α) * " ⪯ " * syntaxstring(z, remove_redundant_parentheses=false))
        println("Height: " * string(height(z)))
        println("Tokens: " * string(ntokens(z)))
        println()
    end
    randombranch(_::ManyValuedTableau) = rand(rng, Int)
    r = manyvaluedmodalsat(SignedFormula(false, (α, z)), a, roundrobin, randombranch; verbose, timeout, kwargs...)
    if isnothing(r)
        return r
    else
        return !r
    end
end
