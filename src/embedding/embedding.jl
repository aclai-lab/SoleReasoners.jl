using Base.Threads: @threads
using SoleLogics: AnyWorld, Atom, BooleanTruth, SyntaxBranch, check

function embed(φ::Union{Atom, BooleanTruth, SyntaxBranch}, e::E; memo::M) where {E<:AbstractVector, M<:AbstractDict}
    return Vector{Bool}(map(m->check(φ, m, AnyWorld(); use_memo=memo[m], memo_max_height=2), e))
end

function sat(φ::Union{Atom, BooleanTruth, SyntaxBranch}, e::E; memo::M) where {E<:AbstractVector, M<:AbstractDict}
    # r = false
    # l = ReentrantLock();
    # @threads for m in e
    for m in e
        if check(φ, m, AnyWorld(); use_memo=memo[m], memo_max_height=2)
            # lock(l) do
                # r = true
            # end
            return true
        end
    end
    return false
end

function unsat(φ::Union{Atom, BooleanTruth, SyntaxBranch}, e::E; memo::M) where {E<:AbstractVector, M<:AbstractDict}
    return !sat(φ, e; memo=memo)
end

function val(φ::Union{Atom, BooleanTruth, SyntaxBranch}, e::E; memo::M) where {E<:AbstractVector, M<:AbstractDict}
    return unsat(¬(φ), e; memo=memo)
end

function unval(φ::Union{Atom, BooleanTruth, SyntaxBranch}, e::E; memo::M) where {E<:AbstractVector, M<:AbstractDict}
    return !val(φ, e; memo=memo)
end

function eqv(φ::Union{Atom, BooleanTruth, SyntaxBranch}, ψ::Union{Atom, BooleanTruth, SyntaxBranch}, e::E; memo::M) where {E<:AbstractVector, M<:AbstractDict}
    return embed(φ, e; memo=memo) == embed(ψ, e; memo=memo)
end

function ent(φ::Union{Atom, BooleanTruth, SyntaxBranch}, ψ::Union{Atom, BooleanTruth, SyntaxBranch}, e::E; memo::M) where {E<:AbstractVector, M<:AbstractDict}
    a = embed(φ, e; memo=memo)
    b = embed(ψ, e; memo=memo)
    return (a .& b) == a
end
