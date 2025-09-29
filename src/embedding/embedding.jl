using SoleLogics: SyntaxBranch, check

function embed(φ::SyntaxBranch, e::E; memo::M) where {E<:AbstractVector, M<:AbstractDict}
    return map(
        m->(
            count(
                map(
                    w->check(φ, m, w; use_memo=memo[m]),
                    m.frame.worlds
                )
            ) > 0
        ),
        e
    )
end

function sat(φ::SyntaxBranch, e::E; memo::M) where {E<:AbstractVector, M<:AbstractDict}
    return count(embed(φ, e; memo=memo)) > 0
end

function unsat(φ::SyntaxBranch, e::E; memo::M) where {E<:AbstractVector, M<:AbstractDict}
    return !sat(φ, e; memo=memo)
end

function val(φ::SyntaxBranch, e::E; memo::M) where {E<:AbstractVector, M<:AbstractDict}
    return unsat(¬(φ), e; memo=memo)
end

function unval(φ::SyntaxBranch, e::E; memo::M) where {E<:AbstractVector, M<:AbstractDict}
    return !val(φ, e; memo=memo)
end

function eqv(φ::SyntaxBranch, ψ::SyntaxBranch, e::E; memo::M) where {E<:AbstractVector, M<:AbstractDict}
    return embed(φ, e; memo=memo) == embed(ψ, e; memo=memo)
end

function ent(φ::SyntaxBranch, ψ::SyntaxBranch, e::E; memo::M) where {E<:AbstractVector, M<:AbstractDict}
    a = embed(φ, e; memo=memo)
    b = embed(ψ, e; memo=memo)
    return (a .&& b) == a
end

function embed0(φ::SyntaxBranch, e::E; memo::M) where {E<:AbstractVector, M<:AbstractDict}
    return map(m->check(φ, m, first(m.frame.worlds); use_memo=memo[m]), e)
end

function sat0(φ::SyntaxBranch, e::E; memo::M) where {E<:AbstractVector, M<:AbstractDict}
    return count(embed0(φ, e; memo)) > 0
end

function unsat0(φ::SyntaxBranch, e::E; memo::M) where {E<:AbstractVector, M<:AbstractDict}
    return !sat0(φ, e; memo=memo)
end

function val0(φ::SyntaxBranch, e::E; memo::M) where {E<:AbstractVector, M<:AbstractDict}
    return unsat0(¬(φ), e; memo=memo)
end

function unval0(φ::SyntaxBranch, e::E; memo::M) where {E<:AbstractVector, M<:AbstractDict}
    return !val0(φ, e; memo=memo)
end

function eqv0(φ::SyntaxBranch, ψ::SyntaxBranch, e::E; memo::M) where {E<:AbstractVector, M<:AbstractDict}
    return embed0(φ, e; memo=memo) == embed0(ψ, e; memo=memo)
end

function ent0(φ::SyntaxBranch, ψ::SyntaxBranch, e::E; memo::M) where {E<:AbstractVector, M<:AbstractDict}
    a = embed0(φ, e; memo=memo)
    b = embed0(ψ, e; memo=memo)
    return (a .&& b) == a
end
