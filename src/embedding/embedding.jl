using Base.Threads: @threads
using SoleLogics: AnyWorld, SyntaxBranch, check
using StaticArrays: SVector

function embed(φ::SyntaxBranch, e::E; memo::M) where {E<:AbstractVector, M<:AbstractDict}
    return SVector{length(e), Bool}(map(m->check(φ, m, AnyWorld(); use_memo=memo[m], memo_max_height=2), e))
end

function sat(φ::SyntaxBranch, e::E; memo::M) where {E<:AbstractVector, M<:AbstractDict}
    # return count(embed(φ, e; memo=memo)) > 0
    @threads for m in e
        if check(φ, m, AnyWorld(); use_memo=memo[m], memo_max_height=2)
            return true
        end
    end
    return false
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
    return (a .& b) == a
end
