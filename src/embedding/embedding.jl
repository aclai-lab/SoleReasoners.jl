using SoleLogics: SyntaxBranch, check

# Embedding
function embed(φ::SyntaxBranch, e::E) where {E<:AbstractVector}
    return map(m->(count(map(w->check(φ, m, w), m.frame.worlds))>0), e)
end
sat(φ::SyntaxBranch, e::E) where {E<:AbstractVector} = count(embed(φ, e))>0
unsat(φ::SyntaxBranch, e::E) where {E<:AbstractVector} = !sat(φ, e)
val(φ::SyntaxBranch, e::E) where {E<:AbstractVector} = unsat(¬(φ), e)
unval(φ::SyntaxBranch, e::E) where {E<:AbstractVector} = !val(φ, e)
function eqv(φ::SyntaxBranch, ψ::SyntaxBranch, e::E) where {E<:AbstractVector}
    return embed(φ, e) == embed(ψ, e)
end
function ent(φ::SyntaxBranch, ψ::SyntaxBranch, e::E) where {E<:AbstractVector}
    a = embed(φ, e)
    b = embed(ψ, e)
    return (a .&& b) == a
end
# # Old version (only on w0)
# function val0(φ::SyntaxBranch, e::E) where {E<:AbstractVector}
#     return countmap(map(x->check(φ, x, first(x.frame.worlds)), e))[0] == 0
# end
# unval0(φ::SyntaxBranch, e::E) where {E<:AbstractVector} = !val0(φ, e)
# function unsat0(φ::SyntaxBranch, e::E) where {E<:AbstractVector}
#     return countmap(map(x->check(φ, x, first(x.frame.worlds)), e))[1] == 0
# end
# sat0(φ::SyntaxBranch, e::E) where {E<:AbstractVector} = !unsat0(φ, e)
