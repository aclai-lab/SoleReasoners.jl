using Base.Threads: @threads
using SoleLogics: AnyWorld, Atom, BooleanTruth, SyntaxBranch, check

function embed(φ::Union{Atom,BooleanTruth,SyntaxBranch}, e::E; memo::M) where {E<:AbstractVector,M<:AbstractDict}
    return Vector{Bool}(map(m -> check(φ, m, AnyWorld(); use_memo=memo[m], memo_max_height=2), e))
end

function sat(φ::Union{Atom,BooleanTruth,SyntaxBranch}, e::E; memo::M) where {E<:AbstractVector,M<:AbstractDict}
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

function unsat(φ::Union{Atom,BooleanTruth,SyntaxBranch}, e::E; memo::M) where {E<:AbstractVector,M<:AbstractDict}
    return !sat(φ, e; memo=memo)
end

function val(φ::Union{Atom,BooleanTruth,SyntaxBranch}, e::E; memo::M) where {E<:AbstractVector,M<:AbstractDict}
    return unsat(¬(φ), e; memo=memo)
end

function unval(φ::Union{Atom,BooleanTruth,SyntaxBranch}, e::E; memo::M) where {E<:AbstractVector,M<:AbstractDict}
    return !val(φ, e; memo=memo)
end

function eqv(φ::Union{Atom,BooleanTruth,SyntaxBranch}, ψ::Union{Atom,BooleanTruth,SyntaxBranch}, e::E; memo::M) where {E<:AbstractVector,M<:AbstractDict}
    return embed(φ, e; memo=memo) == embed(ψ, e; memo=memo)
end

function ent(φ::Union{Atom,BooleanTruth,SyntaxBranch}, ψ::Union{Atom,BooleanTruth,SyntaxBranch}, e::E; memo::M) where {E<:AbstractVector,M<:AbstractDict}
    a = embed(φ, e; memo=memo)
    b = embed(ψ, e; memo=memo)
    return (a .& b) == a
end

using StatsBase
using Graphs
using Random

using SoleLogics
using SoleReasoners


"""
Cosine similarity, but considering that we are dealing with bitstrings.
"""
function similarity(a::Vector{Bool}, b::Vector{Bool})
    numerator = count(a .& b)
    # https://en.wikipedia.org/wiki/Cosine_similarity
    denominator = sqrt(count(a)) * sqrt(count(b))

    return numerator / denominator
end


"""
Check whether the `k`-th row (or column) of the boolean matrix `A` contains 
a similar row (or column).

Two boolean vectors are similar if their [`similaity`](@ref) is higher than `σ`.

Return two integer, the first one referring to rows and the second one referring 
to columns; each integer is the index triggering the high similarity, 
or `nothing` if no similar vectors are found.
"""
function redundant(A::Matrix{Bool}, σ::Float64, k::Int)
    """
    Subroutine of [`redundant`](@ref).

    Consider all the ordered pair of rows in `A` and return a index corresponding
    to the first row that is similar to some other row; return nothing otherwise.
    """
    function _redundant_rows(A::Matrix{Bool}, σ::Float64, k::Int)
        for i in 1:(k-1)
            current_row = A[i, :]
            for j in (i+1):k
                target_row = A[j, :]
                if similarity(current_row, target_row) >= σ
                    return j
                end
            end
        end

        return nothing
    end

    """
    Subroutine of [`redundant`](@ref).

    Consider all the ordered pair of columns in `A` and return a index 
    corresponding to the first row that is similar to some other row; 
    return nothing otherwise.
    """
    function _redundant_cols(A::Matrix{Bool}, σ::Float64, k::Int)
        for i in 1:(k-1)
            current_col = A[:, i]
            for j in (i+1):k
                target_col = A[:, j]
                if similarity(current_col, target_col) >= σ
                    return j
                end
            end
        end

        return nothing
    end

    return _redundant_rows(A, σ, k), _redundant_cols(A, σ, k)
end

"""
Fill the `k`-th row and column of `A` with the results of model checking the 
`k`-th formula to all the models and the `k`-th model to all the formulae.
"""
function eval!(
    A::Matrix{Bool},
    E::Vector{SoleLogics.KripkeStructure},
    F::Vector{SoleLogics.Formula},
    k;
    ROOT_WORLD=SoleLogics.World(1)
)
    A[k, 1:(k-1)] = map(model -> check(F[k], model, ROOT_WORLD), E[1:(k-1)])
    # new model for all the old formulae
    A[1:(k-1), k] = map(formula -> check(formula, E[k], ROOT_WORLD), F[1:(k-1)])
    # the new intersection value
    A[k, k] = check(F[k], E[k], ROOT_WORLD)
end

"""
Create an embedding matrix as specified in the article ..., algorithm ...

# Examples

```julia
Random.seed!(934)
rng = Random.GLOBAL_RNG # AbstractRNG # Xoshiro(934)

N = 20
D = 5
H = 5
alphabet = SoleLogics.Atom.(["p", "q", "r", "s", "t"])
n = 30
MAX_ITERATIONS = 10000
σ = 0.99
ROOT_WORLD = SoleLogics.World(1)

E, F, A = create_adversarial_embedding(N, D, P, alphabet, n, MAX_ITERATIONS, σ;
    rng=rng, ROOT_WORLD=ROOT_WORLD, rich_return=true)
aot = vcat(letters, [⊤, ⊥])
    aotpicker = (rng)->StatsBase.sample(rng, aot, StatsBase.uweights(length(aot)))

# Check that the embedding does respect the similarity threshold σ
unique(eachcol(A))
unique(eachrow(A))
```
"""
function create_adversarial_embedding(
    N::Int, # max number of worlds in a model
    D::Int, # maximal modal depth
    H::Int, # maximal height 
    AP::Vector{<:Atom}, # propositional alphabet
    n::Int, # embedding cardinality
    MAX_ITERATIONS::Int, # maximum number of iterations
    σ::Float64; # similarity threshold
    rng::AbstractRNG,
    connectives=Vector{Connective}([∧, ∨, →, ¬, ◊, □]),
    ROOT_WORLD::SoleLogics.World{Int}=SoleLogics.World(1),
    rich_return::Bool=false, # instead of returning E, return E, A, F
)
    # first part of pseudocode in AAAI2026
    A = zeros(Bool, n, n)
    E = Vector{SoleLogics.KripkeStructure}(undef, n)
    F = Vector{SoleLogics.Formula}(undef, n)

    # boundaries for producing edges
    _nedges_min = N - 1
    _nedges_max = N * (N - 1)

    # utility for putting a letter or a truth value in formulae leaves;
    # aot stands for "atom or truth"
    aot = vcat(AP, [⊤, ⊥])
    aotpicker = (rng) -> StatsBase.sample(rng, aot,
        StatsBase.uweights(length(aot)))

    # AddModel and AddFormula of pseudocode
    # note: the "add" is misleading here, since we are not adding but returning
    add_model = () -> begin
        _nedges = rand(rng, _nedges_min:_nedges_max)
        randmodel(rng, N, _nedges, AP, [⊤, ⊥])
    end
    add_formula = () -> randformula(rng, H, AP, connectives;
        maxmodaldepth=D, mode=:full, basecase=aotpicker)

    k = 1
    E[k] = add_model()
    F[k] = add_formula()
    A[k, k] = check(F[k], E[k], ROOT_WORLD) # just a check on a 1x1 matrix

    while k < n
        iterations = 0 # necessary later for blocking unlucky generations

        # after this assignemnt E[1:(k-1)] are the old models (same for F)
        k += 1
        E[k] = add_model()
        F[k] = add_formula()

        # A = Eval(E, F, k)
        eval!(A, E, F, k; ROOT_WORLD=ROOT_WORLD)

        # IsRedundant(A, σ, k)
        redundant_model_idx, redundant_formula_idx = redundant(A, σ, k)

        # repeat if the new model or the new formula is redundant;
        # instead, if both the redundant indexes are nothing, everything is ok
        while !(isnothing(redundant_model_idx) &&
                isnothing(redundant_formula_idx))

            # distinguish the two cases; note that they are not exclusive
            if !isnothing(redundant_formula_idx)
                F[redundant_formula_idx] = add_formula()

                println(F[redundant_formula_idx])

                A[redundant_formula_idx, 1:k] = map(model -> check(
                        F[redundant_formula_idx], model, ROOT_WORLD), E[1:k])
            end

            if !isnothing(redundant_model_idx)
                E[redundant_model_idx] = add_model()
                A[1:k, redundant_model_idx] = map(formula -> check(
                        formula, E[redundant_model_idx], ROOT_WORLD), F[1:k])
            end

            redundant_model_idx, redundant_formula_idx = redundant(A, σ, k)

            iterations += 1
            if iterations == MAX_ITERATIONS
                println("Early stopping!")
                break
            end
        end
    end

    if rich_return
        return E, F, A
    else
        return E
    end
end



