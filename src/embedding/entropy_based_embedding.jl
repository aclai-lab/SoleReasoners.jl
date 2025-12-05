using Base.Threads: @threads
using SoleLogics: AnyWorld, Atom, BooleanTruth, SyntaxBranch, check

function hamming(u::AbstractVector{Bool}, v::AbstractVector{Bool})
    @assert length(u) == length(v)
    c = 0
    @inbounds for i in eachindex(u, v)
        c += (u[i] ⊻ v[i])  # XOR
    end
    return c
end

function row_entropy(M::AbstractMatrix{Bool})
    n, m = size(M)
    if n < 2
        return 0.0
    end
    acc = 0.0
    cnt = 0
    @inbounds for i in 1:n-1
        ri = view(M, i, :)
        for j in i+1:n
            rj = view(M, j, :)
            acc += hamming(ri, rj) / m
            cnt += 1
        end
    end
    return acc / cnt
end

function col_entropy(M::AbstractMatrix{Bool})
    n, m = size(M)
    if m < 2
        return 0.0
    end
    acc = 0.0
    cnt = 0
    @inbounds for j in 1:m-1
        cj = view(M, :, j)
        for k in j+1:m
            ck = view(M, :, k)
            acc += hamming(cj, ck) / n
            cnt += 1
        end
    end
    return acc / cnt
end

function entropy(M::AbstractMatrix{Bool})
    return row_entropy(M) + col_entropy(M)
end