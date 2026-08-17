using SoleLogics: syntaxstring

"""
    abstract type TableauCertificate end

Abstract supertype for the certificates [`alphasat`](@ref) can optionally
return alongside its verdict, when called with `certificate=true`. Asking for
a certificate never changes the search: every field is built out of tableau
state ([`judgement`](@ref), [`assertion`](@ref), [`world`](@ref),
[`frame`](@ref), [`father`](@ref)) the search already computes while deciding
`true`, `false`, or `nothing`.

Exactly one concrete subtype is produced per outcome:
- [`UnsatCertificate`](@ref) when the verdict is `false`;
- [`SatCertificate`](@ref) when the verdict is `true`;
- [`UndeterminedCertificate`](@ref) when the verdict is `nothing`.

A consumer must branch on which concrete type it received (or on the `kind`
key produced by [`serialize_alphasat`](@ref)) before treating a certificate as
evidence of anything: an [`UndeterminedCertificate`](@ref) is not, and must
never be presented as, a proof of either `true` or `false`.
"""
abstract type TableauCertificate end

"""
    BranchStep

A `NamedTuple` `(judgement, assertion, world)` describing one node along a
tableau branch, in the same shape returned by [`judgement`](@ref),
[`assertion`](@ref) and [`world`](@ref). A `Vector{BranchStep}` in root-to-leaf
order is the branch trace the tableau actually derived.
"""
const BranchStep = NamedTuple{(:judgement, :assertion, :world)}

"""
    branchstep(t::T) where {T<:ManyValuedMultiModalTableau}

Return the [`BranchStep`](@ref) for tableau node `t`.
"""
branchstep(t::T) where {T<:ManyValuedMultiModalTableau} =
    (judgement=judgement(t), assertion=assertion(t), world=world(t))::BranchStep

"""
    branchsteps(t::T) where {T<:ManyValuedMultiModalTableau}

Return the root-to-leaf trace of [`BranchStep`](@ref)s along the branch ending
at `t`, walking [`father`](@ref) pointers. This works even after [`close!`](@ref)
has detached `t` from its father's `children`, since `close!` never clears
`father` itself.
"""
function branchsteps(t::T) where {T<:ManyValuedMultiModalTableau}
    steps = Vector{BranchStep}()
    node = t
    while true
        pushfirst!(steps, branchstep(node))
        isroot(node) && break
        node = father(node)
    end
    return steps
end

"""
    struct BranchClosure
        rule::Symbol
        judgement::Bool
        assertion::Tuple
        world::Any
        witness::Union{Nothing,BranchStep}
        steps::Vector{BranchStep}
    end

One closed branch of the tableau. `steps` is the root-to-leaf
[`branchsteps`](@ref) trace of the branch; `judgement`, `assertion` and
`world` describe the leaf node at which the branch closed; `rule` names which
closure condition fired there, using the same labels as the comments in
`many-valued-multi-modal-tableau/alphasat.jl` (`:X1`, `:X2`, `:X3`, `:X4`,
`:X5`, or `:X5bis`). `witness` is set only for `:X5`/`:X5bis` closures, and is
the earlier [`BranchStep`](@ref) on the same world that the closing node
contradicts.

Each rule is re-checkable against the algebra alone, without re-running the
tableau (`β`, `γ` below are `assertion[1]`, `assertion[2]` converted to
`FiniteTruth`, and `algebra` is the `FiniteFLewAlgebra` the search ran
against):
- `:X1`: `judgement == true`, `assertion == (β, γ)`, and
  `!precedeq(algebra, β, γ)` — the branch asserted `β⪯γ` but the algebra
  refutes it;
- `:X2`: `judgement == false`, `assertion == (β, γ)`, and
  `precedeq(algebra, β, γ)` — the branch asserted `β⪯γ` does *not* hold, but
  the algebra says it does;
- `:X3`: `judgement == false` and either `assertion == (β, γ)` with
  `isbot(β)`, or `assertion == (β, φ)` with `isbot(β)` — `⊥` precedes
  everything, contradicting the `false` judgement;
- `:X4`: `judgement == false` and either `assertion == (β, γ)` with
  `istop(γ)`, or `assertion == (φ, β)` with `istop(β)` — everything precedes
  `⊤`, contradicting the `false` judgement;
- `:X5`/`:X5bis`: `witness` and the closing node share `world` and the same
  formula in `assertion`, with opposite `judgement`s and truth bounds that
  make both hold impossible via `precedeq`.
"""
struct BranchClosure
    rule::Symbol
    judgement::Bool
    assertion::Tuple
    world::Any
    witness::Union{Nothing,BranchStep}
    steps::Vector{BranchStep}
end

"""
    struct UnsatCertificate <: TableauCertificate
        closures::Vector{BranchClosure}
    end

Certificate for an unsatisfiable result (`alphasat` returned `false`): one
[`BranchClosure`](@ref) per branch the search closed. This is the tableau's
proof object, handed back instead of being thrown away.
"""
struct UnsatCertificate <: TableauCertificate
    closures::Vector{BranchClosure}
end

"""
    struct SatCertificate <: TableauCertificate
        worlds::Vector{Any}
        frame::Any
        steps::Vector{BranchStep}
    end

Certificate for a satisfiable result (`alphasat` returned `true`): the open
branch, presented as a model. `frame` is the `ManyValuedLinearOrder` (or tuple
of `ManyValuedLinearOrder`s) the branch settled on; `worlds` lists the
distinct worlds mentioned along the branch; `steps` is the root-to-leaf
[`branchsteps`](@ref) trace, i.e. the truth assignments the branch commits to.
Accessibility edges between any two worlds in `worlds` can be recomputed from
`frame` with `mveval`, without re-running the search.
"""
struct SatCertificate <: TableauCertificate
    worlds::Vector{Any}
    frame::Any
    steps::Vector{BranchStep}
end

"""
    struct UndeterminedCertificate <: TableauCertificate
        reason::Symbol
        cycle::Int
        elapsed::Float64
    end

Certificate for an undetermined result (`alphasat` returned `nothing`). This
records *only* that the search was cut short — `reason` is `:timeout` or
`:memory` — after `cycle` expansion cycles and `elapsed` seconds. It proves
nothing about satisfiability or unsatisfiability, and must never be presented
as if it did: `nothing` is undetermined, not unsatisfiable.
"""
struct UndeterminedCertificate <: TableauCertificate
    reason::Symbol
    cycle::Int
    elapsed::Float64
end

# --- plain Dict serialisation, mirroring SoleLogics' `serialize_check` -----

function _worldids(worlds::AbstractVector)
    Dict{Any,String}(w => "w$(n)" for (n, w) in enumerate(worlds))
end

function _stepdict(step::BranchStep, ids::Dict{Any,String})
    Dict{String,Any}(
        "judgement" => step.judgement,
        "assertion" => [syntaxstring(a) for a in step.assertion],
        "world" => get(ids, step.world, string(step.world)),
    )
end

function _closuredict(c::BranchClosure, ids::Dict{Any,String})
    Dict{String,Any}(
        "rule" => string(c.rule),
        "judgement" => c.judgement,
        "assertion" => [syntaxstring(a) for a in c.assertion],
        "world" => get(ids, c.world, string(c.world)),
        "witness" => isnothing(c.witness) ? nothing : _stepdict(c.witness, ids),
        "steps" => [_stepdict(s, ids) for s in c.steps],
    )
end

function _certworlds(cert::UnsatCertificate)
    worlds = Any[]
    for c in cert.closures
        push!(worlds, c.world)
        !isnothing(c.witness) && push!(worlds, c.witness.world)
        for s in c.steps
            push!(worlds, s.world)
        end
    end
    return unique(worlds)
end
_certworlds(cert::SatCertificate) = unique(vcat(cert.worlds, [s.world for s in cert.steps]))
_certworlds(::UndeterminedCertificate) = Any[]

"""
    certificatedict(cert::TableauCertificate)

Return `cert` as a plain nested `Dict{String,Any}`; see [`serialize_alphasat`](@ref)
for the documented shape. No JSON package is required or added: callers
serialise the returned `Dict` themselves (e.g. `JSON3.write(certificatedict(cert))`).
A satisfiable certificate's frame is represented by nested dictionaries with
`"kind" => "linear_order"`, integer truth-value matrices under `"lt"` and
`"eq"`, or `"kind" => "product"` with component orders under `"orders"`.
"""
function certificatedict(cert::UnsatCertificate)
    ids = _worldids(_certworlds(cert))
    Dict{String,Any}(
        "kind" => "unsat",
        "closures" => [_closuredict(c, ids) for c in cert.closures],
    )
end
# Keep the serialised frame independent of StaticArrays and of Julia's
# `ManyValuedLinearOrder` representation. Matrix entries are the stable
# `FiniteTruth.index` values; an independent checker reconstructs them in the
# algebra it already has.
_truthindex(x) = hasproperty(x, :index) ? getproperty(x, :index) : string(x)
function _matrixvalues(m)
    rows = Any[]
    for i in axes(m, 1)
        push!(rows, Any[_truthindex(m[i, j]) for j in axes(m, 2)])
    end
    rows
end
function _framedict(frame)
    if frame isa Tuple
        return Dict{String,Any}(
            "kind" => "product",
            "orders" => [_framedict(f) for f in frame],
        )
    elseif hasproperty(frame, :mvlt) && hasproperty(frame, :mveq)
        return Dict{String,Any}(
            "kind" => "linear_order",
            "lt" => _matrixvalues(getproperty(frame, :mvlt)),
            "eq" => _matrixvalues(getproperty(frame, :mveq)),
        )
    else
        error("cannot serialise tableau frame of type $(typeof(frame))")
    end
end

function certificatedict(cert::SatCertificate)
    ids = _worldids(_certworlds(cert))
    Dict{String,Any}(
        "kind" => "sat",
        "worlds" => [ids[w] for w in cert.worlds],
        "frame" => _framedict(cert.frame),
        "steps" => [_stepdict(s, ids) for s in cert.steps],
    )
end
function certificatedict(cert::UndeterminedCertificate)
    Dict{String,Any}(
        "kind" => "undetermined",
        "reason" => string(cert.reason),
        "cycle" => cert.cycle,
        "elapsed" => cert.elapsed,
    )
end

"""
    serialize_alphasat(result::Union{Bool,Nothing}, cert::Union{Nothing,TableauCertificate})

Return `(result, cert)` — as produced by `alphasat(...; certificate=true)` —
as a plain nested `Dict{String,Any}` with keys:
- `"schema_version"`: `"solereasoners.alphasat.v1"`;
- `"result"`: `true`, `false`, or `nothing`;
- `"certificate"`: `nothing` when `cert` is `nothing` (i.e. `certificate` was
  not requested), otherwise `certificatedict(cert)`, whose `"kind"` key is
  `"unsat"`, `"sat"`, or `"undetermined"` and matches `result` (`false`,
  `true`, `nothing` respectively).

No JSON package is required or added; callers serialise the returned `Dict`
themselves, exactly as SoleLogics' `serialize_check` does.
"""
function serialize_alphasat(
    result::Union{Bool,Nothing},
    cert::Union{Nothing,TableauCertificate}=nothing
)
    Dict{String,Any}(
        "schema_version" => "solereasoners.alphasat.v1",
        "result" => result,
        "certificate" => isnothing(cert) ? nothing : certificatedict(cert),
    )
end
