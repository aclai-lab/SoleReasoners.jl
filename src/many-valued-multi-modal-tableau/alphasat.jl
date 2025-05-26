using SoleLogics: Formula, Truth, syntaxstring, token, NamedConnective
using SoleLogics: BoxRelationalConnective, DiamondRelationalConnective
using SoleLogics: children as subformulas, relation
using SoleLogics.ManyValuedLogics: FiniteFLewAlgebra, FiniteTruth
using SoleLogics.ManyValuedLogics: precedeq, getdomain
using SoleLogics.ManyValuedLogics: maximalmembers, minimalmembers

function findsimilar(
    tableau::T,
    algebra::FiniteFLewAlgebra
) where {
    T<:ManyValuedMultiModalTableau
}
    ψ = assertion(tableau)[2]
    if judgement(tableau)
        γ = assertion(tableau)[1]
        # Looking for false(β⪯ψ, ...) where β⪯γ
        while !isroot(tableau)
            tableau = tableau.father
            if !judgement(tableau)
                if assertion(tableau)[1] isa Truth && assertion(tableau)[2] == ψ
                    β = convert(FiniteTruth, assertion(tableau)[1])::FiniteTruth
                    if precedeq(algebra, β, γ)
                        return true
                    end
                end
            end
        end
    else
        β = assertion(tableau)[1]
        # Looking for true(γ⪯ψ, ...) where β⪯γ
        while !isroot(tableau)
            tableau = tableau.father
            if judgement(tableau)
                if assertion(tableau)[1] isa Truth && assertion(tableau)[2] == ψ
                    γ = convert(FiniteTruth, assertion(tableau)[1])::FiniteTruth
                    if precedeq(algebra, β, γ)
                        return true
                    end
                end
            end
        end
    end
    return false
end

function findtableau(
    tableau::T,
    j::Bool,
    φ::NTuple{2,Formula},
    w::W
) where {
    T<:ManyValuedMultiModalTableau,
    W
}
    if judgement(tableau) == j && assertion(tableau) == φ && world(tableau) == w
        return true
    end
    while !isroot(tableau)
        tableau = father(tableau)
        if judgement(tableau) == j &&
           assertion(tableau) == φ &&
           world(tableau) == w
            return true
        end
    end
    return false
end

function alphasat(
    metricheaps::Vector{MetricHeap},
    choosenode::F,
    algebra::FiniteFLewAlgebra;
    timeout::Union{Nothing, Int} = nothing
) where {
    F<:Function
}
    cycle = 1
    t0 = time_ns()
    while true
        if !isnothing(timeout) && (time_ns()-t0)/1e9 > timeout
            @warn "Timeout"
            return nothing
        end
        # if using too much memory, try to free memory calling full GC sweep
        if cycle%100==0 && getfreemem() < gettotmem()*5e-2
            @warn "Calling Garbage Collector"
            GC.gc()
        end
        # if using too much memory, kill execution to avoid crashes
        if cycle%100==0 && getfreemem() < gettotmem()*5e-2
            @warn "Too much memory being used, exiting"
            return nothing
        end
        node = choosenode(metricheaps, cycle)
        isnothing(node) && return false # all branches are closed
        if expanded(node)
            # DEBUG (satisfiable branch)
            # println(node.frame)
            # result = [node]
            # while (!isroot(node))
            #     node = node.father
            #     push!(result, node)
            # end
            # for r in reverse(result) println(r) end
            return true   # found a satisfiable branch
        end
        expansionnode = findexpansionnode(node)
        # println("$cycle\t$expansionnode") # DEBUG (expansion node)
        expand!(expansionnode)
        if assertion(expansionnode) isa Tuple{Truth, Truth}
            # β ⪯ γ
            β = convert(FiniteTruth, assertion(expansionnode)[1])::FiniteTruth
            γ = convert(FiniteTruth, assertion(expansionnode)[2])::FiniteTruth
            if judgement(expansionnode) && !precedeq(algebra, β, γ)
                close!(expansionnode)  # X1
            elseif !judgement(expansionnode) &&
                (isbot(β) || istop(γ) || precedeq(algebra, β, γ))  # X3, X4, X2
                    close!(expansionnode)
            else
                # no condition matched, push node back into metricheaps
                push!(metricheaps, node)
            end
        elseif assertion(expansionnode) isa Tuple{Truth, Formula}
            # β ⪯ φ
            β = convert(FiniteTruth, assertion(expansionnode)[1])::FiniteTruth
            φ = assertion(expansionnode)[2]
            if !judgement(expansionnode) && isbot(β)
                close!(expansionnode)   # X3
            elseif findsimilar(expansionnode, algebra)
                close!(expansionnode)   # X5
            elseif token(φ) isa NamedConnective{:∧} && !isbot(β)
                (ψ, ε) = subformulas(φ)
                pairs = Set{NTuple{2,FiniteTruth}}()
                if judgement(expansionnode)
                    # T∧
                    for βi ∈ getdomain(algebra)
                        for γi ∈ getdomain(algebra)
                            if precedeq(algebra, β, algebra.monoid(βi, γi))
                                push!(pairs, (βi, γi))
                            end
                        end
                    end
                    for p ∈ pairs
                        for q ∈ pairs
                            if precedeq(algebra, q[1], p[1]) &&
                               precedeq(algebra, q[2], p[2]) &&
                               p != q
                                delete!(pairs, p)
                            end
                        end
                    end
                    for leaf ∈ findleaves(expansionnode)
                        for pair ∈ pairs
                            if !findtableau(
                                leaf,
                                true,
                                (pair[1], ψ),
                                world(expansionnode)
                            )
                                t1 = typeof(expansionnode)(
                                    true,
                                    (pair[1], ψ),
                                    world(expansionnode),
                                    frame(leaf),
                                    leaf
                                )
                                push!(metricheaps, t1)
                                if !findtableau(
                                    t1,
                                    true,
                                    (pair[2], ε),
                                    world(expansionnode)
                                )
                                    t2 = typeof(expansionnode)(
                                        true,
                                        (pair[2], ε),
                                        world(expansionnode),
                                        frame(t1),
                                        t1
                                    )
                                    push!(metricheaps, t2)
                                end
                            else
                                if !findtableau(
                                    leaf,
                                    true,
                                    (pair[2], ε),
                                    world(expansionnode)
                                )
                                    t = typeof(expansionnode)(
                                        true,
                                        (pair[2], ε),
                                        world(expansionnode),
                                        frame(leaf),
                                        leaf
                                    )
                                    push!(metricheaps, t)
                                else
                                    # here there should be a branch and one
                                    # should keep track of it using a fake node
                                    # which is always true
                                    t = typeof(expansionnode)(
                                        true,
                                        (FiniteTruth(1), FiniteTruth(1)),
                                        world(expansionnode),
                                        frame(leaf),
                                        leaf
                                    )
                                    push!(metricheaps, t)
                                end
                            end
                        end
                        if isempty(pairs) && leaf == node
                            push!(metricheaps, node)
                        end
                    end
                else
                    # F∧
                    for βi ∈ getdomain(algebra)
                        for γi ∈ getdomain(algebra)
                            if !precedeq(algebra, β, algebra.monoid(βi, γi))
                                push!(pairs, (βi, γi))
                            end
                        end
                    end
                    for p ∈ pairs
                        for q ∈ pairs
                            if precedeq(algebra, p[1], q[1]) &&
                               precedeq(algebra, p[2], q[2]) &&
                               p != q
                                delete!(pairs, p)
                            end
                        end
                    end
                    for leaf ∈ findleaves(expansionnode)
                        for pair ∈ pairs
                            if !findtableau(
                                leaf,
                                true,
                                (ψ, pair[1]),
                                world(expansionnode)
                            )
                                t1 = typeof(expansionnode)(
                                    true,
                                    (ψ, pair[1]),
                                    world(expansionnode),
                                    frame(leaf),
                                    leaf
                                )
                                push!(metricheaps, t1)
                                if !findtableau(
                                    t1,
                                    true,
                                    (ε, pair[2]),
                                    world(expansionnode)
                                )
                                    t2 = typeof(expansionnode)(
                                        true,
                                        (ε, pair[2]),
                                        world(expansionnode),
                                        frame(t1),
                                        t1
                                    )
                                    push!(metricheaps, t2)
                                end
                            else
                                if !findtableau(
                                    leaf,
                                    true,
                                    (ε, pair[2]),
                                    world(expansionnode)
                                )
                                    t = typeof(expansionnode)(
                                        true,
                                        (ε, pair[2]),
                                        world(expansionnode),
                                        frame(leaf),
                                        leaf
                                    )
                                    push!(metricheaps, t)
                                else
                                    # here there should be a branch and one
                                    # should keep track of it using a fake node
                                    # which is always true
                                    t = typeof(expansionnode)(
                                        true,
                                        (FiniteTruth(1), FiniteTruth(1)),
                                        world(expansionnode),
                                        frame(leaf),
                                        leaf
                                    )
                                    push!(metricheaps, t)
                                end
                            end
                        end
                        if isempty(pairs) && leaf == node
                            push!(metricheaps, node)
                        end
                    end
                end
            elseif token(φ) isa NamedConnective{:→} && !isbot(β)
                (ψ, ε) = subformulas(φ)
                pairs = Set{NTuple{2,FiniteTruth}}()
                if judgement(expansionnode)
                    # T→
                    for βi ∈ getdomain(algebra)
                        for γi ∈ getdomain(algebra)
                            if precedeq(algebra, β, algebra.implication(βi, γi))
                                push!(pairs, (βi, γi))
                            end
                        end
                    end
                    for p in pairs
                        for q in pairs
                            if precedeq(algebra, p[1], q[1]) &&
                               precedeq(algebra, q[2], p[2]) &&
                               p != q
                                delete!(pairs, p)
                            end
                        end
                    end
                    for leaf ∈ findleaves(expansionnode)
                        for pair in pairs
                            if !findtableau(
                                leaf,
                                true,
                                (ψ, pair[1]),
                                world(expansionnode)
                            )
                                t1 = typeof(expansionnode)(
                                    true,
                                    (ψ, pair[1]),
                                    world(expansionnode),
                                    frame(leaf),
                                    leaf
                                )
                                push!(metricheaps, t1)
                                if !findtableau(
                                    t1,
                                    true,
                                    (pair[2], ε),
                                    world(expansionnode)
                                )
                                    t2 = typeof(expansionnode)(
                                        true,
                                        (pair[2], ε),
                                        world(expansionnode),
                                        frame(t1),
                                        t1
                                    )
                                    push!(metricheaps, t2)
                                end
                            else
                                if !findtableau(
                                    leaf,
                                    true,
                                    (pair[2], ε),
                                    world(expansionnode)
                                )
                                    t = typeof(expansionnode)(
                                        true,
                                        (pair[2], ε),
                                        world(expansionnode),
                                        frame(leaf),
                                        leaf
                                    )
                                    push!(metricheaps, t)
                                else
                                    # here there should be a branch and one
                                    # should keep track of it using a fake node
                                    # which is always true
                                    t = typeof(expansionnode)(
                                        true,
                                        (FiniteTruth(1), FiniteTruth(1)),
                                        world(expansionnode),
                                        frame(leaf),
                                        leaf
                                    )
                                    push!(metricheaps, t)
                                end
                            end
                        end
                        if isempty(pairs) && leaf == node
                            push!(metricheaps, node)
                        end
                    end
                else
                    # F→
                    for βi ∈ getdomain(algebra)
                        for γi ∈ getdomain(algebra)
                            if !precedeq(
                                algebra,
                                β,
                                algebra.implication(βi, γi)
                            )
                                push!(pairs, (βi, γi))
                            end
                        end
                    end
                    for p in pairs
                        for q in pairs
                            if precedeq(algebra, q[1], p[1]) &&
                               precedeq(algebra, p[2], q[2]) &&
                               p != q
                                delete!(pairs, p)
                            end
                        end
                    end
                    for leaf ∈ findleaves(expansionnode)
                        for pair in pairs
                            if !findtableau(
                                leaf,
                                true,
                                (pair[1], ψ),
                                world(expansionnode)
                            )
                                t1 = typeof(expansionnode)(
                                    true,
                                    (pair[1], ψ),
                                    world(expansionnode),
                                    frame(leaf),
                                    leaf
                                )
                                push!(metricheaps, t1)
                                if !findtableau(
                                    t1,
                                    true,
                                    (ε, pair[2]),
                                    world(expansionnode)
                                )
                                    t2 = typeof(expansionnode)(
                                        true,
                                        (ε, pair[2]),
                                        world(expansionnode),
                                        frame(t1),
                                        t1
                                    )
                                    push!(metricheaps, t2)
                                end
                            else
                                if !findtableau(
                                    leaf,
                                    true,
                                    (ε, pair[2]),
                                    world(expansionnode)
                                )
                                    t2 = typeof(expansionnode)(
                                        true,
                                        (ε, pair[2]),
                                        world(expansionnode),
                                        frame(leaf),
                                        leaf
                                    )
                                    push!(metricheaps, t2)
                                else
                                    # here there should be a branch and one
                                    # should keep track of it using a fake node
                                    # which is always true
                                    t = typeof(expansionnode)(
                                        true,
                                        (FiniteTruth(1), FiniteTruth(1)),
                                        world(expansionnode),
                                        frame(leaf),
                                        leaf
                                    )
                                    push!(metricheaps, t)
                                end
                            end
                        end
                        if isempty(pairs) && leaf == node
                            push!(metricheaps, node)
                        end
                    end
                end
            elseif token(φ) isa BoxRelationalConnective && !isbot(β)
                ψ = subformulas(φ)[1]
                if judgement(expansionnode)
                    # T□"
                    for leaf ∈ findleaves(expansionnode)
                        r = relation(token(φ))
                        w = world(expansionnode)
                        f = frame(leaf)
                        ti = leaf
                        newnodes = false
                        for wi in worlds(typeof(expansionnode), frame(leaf))
                            βi = mveval(r, w, wi, f)
                            γ = algebra.monoid(β, βi)
                            if !isbot(γ)
                                if !findtableau(ti, true, (γ, ψ), wi)
                                    newnodes = true
                                    ti = typeof(expansionnode)(
                                        true,
                                        (γ, ψ),
                                        wi,
                                        f,
                                        ti
                                    )
                                    push!(metricheaps, ti)
                                end
                            end
                        end
                        if !newnodes && leaf == expansionnode
                            return true # found satisfiable branch
                        else
                            ti = typeof(expansionnode)(
                                true,
                                (β, φ),
                                w,
                                f,
                                ti
                            )
                            push!(metricheaps, ti)
                        end
                    end
                else
                    # F□
                    for leaf ∈ findleaves(expansionnode)
                        newleaves = false    
                        r = relation(token(φ))
                        w = world(expansionnode)
                        frames = newframes(leaf, algebra; timeout=timeout, t0=t0)
                        if isnothing(frames)
                            @warn "Timeout"
                            return nothing
                        end
                        for fi in frames
                            for wi in worlds(typeof(expansionnode), fi)
                                βi = mveval(r, w, wi, fi)
                                γ = algebra.monoid(β, βi)
                                if !isbot(γ)
                                    ti = typeof(expansionnode)(
                                        false,
                                        (γ, ψ),
                                        wi,
                                        fi,
                                        leaf
                                    )
                                    push!(metricheaps, ti)
                                    newleaves = true
                                end
                            end
                        end
                        if !newleaves && leaf == node
                            push!(metricheaps, node)
                        end
                    end
                end
            elseif !isbot(β)
                if judgement(expansionnode)
                    # T⪰
                    for leaf ∈ findleaves(expansionnode)
                        ti = leaf
                        newnodes = false
                        for γ in maximalmembers(algebra, β)
                            if !findtableau(
                                ti,
                                false,
                                (φ, γ),
                                world(expansionnode)
                            )
                                newnodes = true
                                ti = typeof(expansionnode)(
                                    false,
                                    (φ, γ),
                                    world(expansionnode),
                                    frame(ti),
                                    ti
                                )
                                push!(metricheaps, ti)
                            end
                        end
                        if !newnodes && leaf == node
                            push!(metricheaps, node)
                        end
                    end
                else
                    # F⪰
                    for leaf ∈ findleaves(expansionnode)
                        for βi in maximalmembers(algebra, β)
                            if !findtableau(
                                leaf,
                                true,
                                (φ, βi),
                                world(expansionnode)
                            )
                                ti = typeof(expansionnode)(
                                    true,
                                    (φ, βi),
                                    world(expansionnode),
                                    frame(leaf),
                                    leaf
                                )
                                push!(metricheaps, ti)
                            else
                                # here there should be a branch and one
                                # should keep track of it using a fake node
                                # which is always true
                                ti = typeof(expansionnode)(
                                    true,
                                    (FiniteTruth(1), FiniteTruth(1)),
                                    world(expansionnode),
                                    frame(leaf),
                                    leaf
                                )
                                push!(metricheaps, ti)
                            end
                        end
                        if isempty(maximalmembers(algebra, β)) && leaf == node
                            push!(metricheaps, node)
                        end
                    end
                end
            else
                # no condition matched, push node back into metricheaps
                push!(metricheaps, node)                
            end
        elseif assertion(expansionnode) isa Tuple{Formula, Truth}
            # φ ⪯ β
            φ = assertion(expansionnode)[1]
            β = convert(FiniteTruth, assertion(expansionnode)[2])::FiniteTruth
            if !judgement(expansionnode) && istop(β)
                close!(expansionnode)   # X4
            elseif token(φ) isa NamedConnective{:∨} && !istop(β)
                (ψ, ε) = subformulas(φ)
                pairs = Set{NTuple{2,FiniteTruth}}()
                if judgement(expansionnode)
                    # T∨
                    for βi ∈ getdomain(algebra)
                        for γi ∈ getdomain(algebra)
                            if precedeq(algebra,  algebra.join(βi, γi), β)
                                push!(pairs, (βi, γi))
                            end
                        end
                    end
                    for p ∈ pairs
                        for q ∈ pairs
                            if precedeq(algebra, p[1], q[1]) &&
                               precedeq(algebra, p[2], q[2]) &&
                               p != q
                                delete!(pairs, p)
                            end
                        end
                    end
                    for leaf ∈ findleaves(expansionnode)
                        for pair ∈ pairs
                            if !findtableau(
                                leaf,
                                true,
                                (ψ, pair[1]),
                                world(expansionnode)
                            )
                                t1 = typeof(expansionnode)(
                                    true,
                                    (ψ, pair[1]),
                                    world(expansionnode),
                                    frame(leaf),
                                    leaf
                                )
                                push!(metricheaps, t1)
                                if !findtableau(
                                    t1,
                                    true,
                                    (ε, pair[2]),
                                    world(expansionnode)
                                )
                                    t2 = typeof(expansionnode)(
                                        true,
                                        (ε, pair[2]),
                                        world(expansionnode),
                                        frame(t1),
                                        t1
                                    )
                                    push!(metricheaps, t2)
                                end
                            else
                                if !findtableau(
                                    leaf,
                                    true,
                                    (ε, pair[2]),
                                    world(expansionnode)
                                )
                                    t = typeof(expansionnode)(
                                        true,
                                        (ε, pair[2]),
                                        world(expansionnode),
                                        frame(leaf),
                                        leaf
                                    )
                                    push!(metricheaps, t)
                                else
                                    # here there should be a branch and one
                                    # should keep track of it using a fake node
                                    # which is always true
                                    t = typeof(expansionnode)(
                                        true,
                                        (FiniteTruth(1), FiniteTruth(1)),
                                        world(expansionnode),
                                        frame(leaf),
                                        leaf
                                    )
                                    push!(metricheaps, t)
                                end
                            end
                        end
                        if isempty(pairs) && leaf == node
                            push!(metricheaps, node)
                        end
                    end
                else
                    # F∨
                    for βi ∈ getdomain(algebra)
                        for γi ∈ getdomain(algebra)
                            if !precedeq(algebra, algebra.join(βi, γi), β)
                                push!(pairs, (βi, γi))
                            end
                        end
                    end
                    for p ∈ pairs
                        for q ∈ pairs
                            if precedeq(algebra, q[1], p[1]) &&
                               precedeq(algebra, q[2], p[2]) &&
                               p != q
                                delete!(pairs, p)
                            end
                        end
                    end
                    for leaf ∈ findleaves(expansionnode)
                        for pair ∈ pairs
                            if !findtableau(
                                leaf,
                                true,
                                (pair[1], ψ),
                                world(expansionnode)
                            )
                                t1 = typeof(expansionnode)(
                                    true,
                                    (pair[1], ψ),
                                    world(expansionnode),
                                    frame(leaf),
                                    leaf
                                )
                                push!(metricheaps, t1)
                                if !findtableau(
                                    t1,
                                    true,
                                    (pair[2], ε),
                                    world(expansionnode)
                                )
                                    t2 = typeof(expansionnode)(
                                        true,
                                        (pair[2], ε),
                                        world(expansionnode),
                                        frame(t1),
                                        t1
                                    )
                                    push!(metricheaps, t2)
                                end
                            else
                                if !findtableau(
                                    leaf,
                                    true,
                                    (pair[2], ε),
                                    world(expansionnode)
                                )
                                    t = typeof(expansionnode)(
                                        true,
                                        (pair[2], ε),
                                        world(expansionnode),
                                        frame(leaf),
                                        leaf
                                    )
                                    push!(metricheaps, t)
                                else
                                    # here there should be a branch and one
                                    # should keep track of it using a fake node
                                    # which is always true
                                    t = typeof(expansionnode)(
                                        true,
                                        (FiniteTruth(1), FiniteTruth(1)),
                                        world(expansionnode),
                                        frame(leaf),
                                        leaf
                                    )
                                    push!(metricheaps, t)
                                end
                            end
                        end
                        if isempty(pairs) && leaf == node
                            push!(metricheaps, node)
                        end
                    end
                end
            elseif token(φ) isa DiamondRelationalConnective && !istop(β)
                ψ = subformulas(φ)[1]
                if judgement(expansionnode)
                    # T◊"
                    for leaf ∈ findleaves(expansionnode)
                        r = relation(token(φ))
                        w = world(expansionnode)
                        f = frame(leaf)
                        ti = leaf
                        newnodes = false
                        for wi in worlds(typeof(expansionnode), frame(leaf))
                            βi = mveval(r, w, wi, f)
                            γ = algebra.implication(βi, β)
                            if !istop(γ)
                                if !findtableau(ti, true, (ψ, γ), wi)
                                    newnodes = true
                                    ti = typeof(expansionnode)(
                                        true,
                                        (ψ, γ),
                                        wi,
                                        f,
                                        ti
                                    )
                                    push!(metricheaps, ti)
                                end
                            end
                        end
                        if !newnodes && leaf == expansionnode
                            return true # found satisfiable branch
                        else
                            ti = typeof(expansionnode)(
                                true,
                                (φ, β),
                                w,
                                f,
                                ti
                            )
                            push!(metricheaps, ti)
                        end
                    end
                else
                    # F◊
                    for leaf ∈ findleaves(expansionnode)
                        newleaves = false    
                        r = relation(token(φ))
                        w = world(expansionnode)
                        frames = newframes(leaf, algebra; timeout=timeout, t0=t0)
                        if isnothing(frames)
                            @warn "Timeout"
                            return nothing
                        end
                        for fi in frames
                            for wi in worlds(typeof(expansionnode), fi)
                                βi = mveval(r, w, wi, fi)
                                γ = algebra.implication(βi, β)
                                if !istop(γ)
                                    ti = typeof(expansionnode)(
                                        false,
                                        (ψ, γ),
                                        wi,
                                        fi,
                                        leaf
                                    )
                                    push!(metricheaps, ti)
                                    newleaves = true
                                end
                            end
                        end
                        if !newleaves && leaf == node
                            push!(metricheaps, node)
                        end
                    end
                end
            elseif !istop(β)
                if judgement(expansionnode)
                    # T⪯
                    for leaf ∈ findleaves(expansionnode)
                        ti = leaf
                        newnodes = false
                        for γ in minimalmembers(algebra, β)
                            if !findtableau(
                                ti,
                                false,
                                (γ, φ),
                                world(expansionnode)
                            )
                                newnodes = true
                                ti = typeof(expansionnode)(
                                    false,
                                    (γ, φ),
                                    world(expansionnode),
                                    frame(ti),
                                    ti
                                )
                                push!(metricheaps, ti)
                            end
                        end
                        if !newnodes && leaf == node
                            push!(metricheaps, node)
                        end
                    end
                else
                    # F⪯
                    for leaf ∈ findleaves(expansionnode)
                        for βi in minimalmembers(algebra, β)
                            if !findtableau(
                                leaf,
                                true,
                                (βi, φ),
                                world(expansionnode)
                            )
                                ti = typeof(expansionnode)(
                                    true,
                                    (βi, φ),
                                    world(expansionnode),
                                    frame(leaf),
                                    leaf
                                )
                                push!(metricheaps, ti)
                            else
                                # here there should be a branch and one
                                # should keep track of it using a fake node
                                # which is always true
                                ti = typeof(expansionnode)(
                                    true,
                                    (FiniteTruth(1), FiniteTruth(1)),
                                    world(expansionnode),
                                    frame(leaf),
                                    leaf
                                )
                                push!(metricheaps, ti)
                            end
                        end
                        if isempty(minimalmembers(algebra, β)) && leaf == node
                            push!(metricheaps, node)
                        end
                    end
                end
            else
                # no condition matched, push node back into metricheaps
                push!(metricheaps, node)                
            end
        else
            error("Unexpected error")
        end
        cycle += 1
    end
end

function alphasat(
    ::T,
    α::T1,
    φ::Formula,
    algebra::FiniteFLewAlgebra,
    choosenode::Function,
    metrics::Function...;
    kwargs...
) where {
    T<:ManyValuedMultiModalTableau,
    T1<:Truth
}
    error("Please, specify `alphasat` for `$T<:ManyValuedMultiModalTableau`")
end

function alphaval(
    ::T,
    α::T1,
    φ::Formula,
    algebra::FiniteFLewAlgebra,
    choosenode::Function,
    metrics::Function...;
    kwargs...
) where {
    T<:ManyValuedMultiModalTableau,
    T1<:Truth
}
    error("Please, specify `alphasat` for `$T<:ManyValuedMultiModalTableau`")
end
