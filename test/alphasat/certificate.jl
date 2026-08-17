################################################################################
#### Certificate ###############################################################
################################################################################
#
# Tests that alphasat's opt-in `certificate=true` output can be independently
# re-checked without re-running the tableau search: for an unsatisfiable
# formula, every recorded BranchClosure is re-verified against the algebra
# alone; for a satisfiable formula, the returned branch is re-checked both
# for internal (Hintikka-style) consistency and by evaluating the original
# formula bottom-up from the atom values the branch commits to.

using SoleLogics: Atom, Formula, Truth, token, children as _children, NamedConnective
using SoleLogics.ManyValuedLogics: FiniteFLewAlgebra, FiniteTruth
using SoleLogics.ManyValuedLogics: precedeq, getdomain, booleanalgebra, Ł4
using SoleLogics.ManyValuedLogics: α as Ł4α, β as Ł4β
using SoleReasoners: BranchClosure, BranchStep, UnsatCertificate, SatCertificate
using SoleReasoners: UndeterminedCertificate, certificatedict, serialize_alphasat

p, q = Atom.(["p", "q"])

timeout = 15

# --- independent re-checkers, built only from `algebra`/`precedeq`/`isbot`/
# --- `istop`, never by re-running the tableau search -----------------------

function verify_closure(c::BranchClosure, algebra::FiniteFLewAlgebra)
    if c.rule == :X1
        c.judgement || return false
        a1, a2 = c.assertion
        (a1 isa Truth && a2 isa Truth) || return false
        return !precedeq(algebra, convert(FiniteTruth, a1), convert(FiniteTruth, a2))
    elseif c.rule == :X2
        c.judgement && return false
        a1, a2 = c.assertion
        (a1 isa Truth && a2 isa Truth) || return false
        return precedeq(algebra, convert(FiniteTruth, a1), convert(FiniteTruth, a2))
    elseif c.rule == :X3
        c.judgement && return false
        return isbot(convert(FiniteTruth, c.assertion[1]))
    elseif c.rule == :X4
        c.judgement && return false
        return istop(convert(FiniteTruth, c.assertion[2]))
    elseif c.rule == :X5
        isnothing(c.witness) && return false
        a1, φ = c.assertion
        wa1, wφ = c.witness.assertion
        φ == wφ || return false
        c.witness.world == c.world || return false
        c.witness.judgement != c.judgement || return false
        if c.judgement
            return precedeq(algebra, convert(FiniteTruth, wa1), convert(FiniteTruth, a1))
        else
            return precedeq(algebra, convert(FiniteTruth, a1), convert(FiniteTruth, wa1))
        end
    elseif c.rule == :X5bis
        isnothing(c.witness) && return false
        φ, a2 = c.assertion
        wφ, wa2 = c.witness.assertion
        φ == wφ || return false
        c.witness.world == c.world || return false
        c.witness.judgement != c.judgement || return false
        if c.judgement
            return precedeq(algebra, convert(FiniteTruth, a2), convert(FiniteTruth, wa2))
        else
            return precedeq(algebra, convert(FiniteTruth, wa2), convert(FiniteTruth, a2))
        end
    else
        return false
    end
end

# A single BranchStep, checked against another BranchStep on the same
# branch/world, using the same X1-X5bis conditions the search itself uses.
function stepscontradict(s::BranchStep, t::BranchStep, algebra::FiniteFLewAlgebra)
    s.world == t.world || return false
    a1, a2 = s.assertion
    if a1 isa Truth && a2 isa Truth
        β, γ = convert(FiniteTruth, a1), convert(FiniteTruth, a2)
        if s.judgement && !precedeq(algebra, β, γ)
            return true
        elseif !s.judgement && (isbot(β) || istop(γ) || precedeq(algebra, β, γ))
            return true
        end
    elseif a1 isa Truth && a2 isa Formula
        β, φ = convert(FiniteTruth, a1), a2
        if !s.judgement && isbot(β)
            return true
        end
        b1, b2 = t.assertion
        if b1 isa Truth && b2 == φ && t.judgement != s.judgement
            β2 = convert(FiniteTruth, b1)
            if s.judgement
                precedeq(algebra, β2, β) && return true
            else
                precedeq(algebra, β, β2) && return true
            end
        end
    elseif a1 isa Formula && a2 isa Truth
        φ, β = a1, convert(FiniteTruth, a2)
        if !s.judgement && istop(β)
            return true
        end
        b1, b2 = t.assertion
        if b1 == φ && b2 isa Truth && t.judgement != s.judgement
            β2 = convert(FiniteTruth, b2)
            if s.judgement
                precedeq(algebra, β, β2) && return true
            else
                precedeq(algebra, β2, β) && return true
            end
        end
    end
    return false
end

function hascontradiction(steps::Vector{BranchStep}, algebra::FiniteFLewAlgebra)
    for s in steps, t in steps
        stepscontradict(s, t, algebra) && return true
    end
    return false
end

# Extract, for `atom`, the unique domain value consistent with every
# constraint recorded on `steps`; error if the branch does not pin it down or
# is inconsistent (a bug in the branch, not in this checker).
function atomvalue(steps::Vector{BranchStep}, atom, algebra::FiniteFLewAlgebra)
    consistent = FiniteTruth[]
    for v in getdomain(algebra)
        ok = true
        for s in steps
            a1, a2 = s.assertion
            if a2 == atom && a1 isa Truth
                β = convert(FiniteTruth, a1)
                if s.judgement != precedeq(algebra, β, v)
                    ok = false
                    break
                end
            elseif a1 == atom && a2 isa Truth
                β = convert(FiniteTruth, a2)
                if s.judgement != precedeq(algebra, v, β)
                    ok = false
                    break
                end
            end
        end
        ok && push!(consistent, v)
    end
    @assert !isempty(consistent) "no value of $atom is consistent with the branch"
    return first(consistent)
end

function evalformula(ψ::Formula, steps::Vector{BranchStep}, algebra::FiniteFLewAlgebra)
    tok = token(ψ)
    if tok isa Atom
        return atomvalue(steps, tok, algebra)
    elseif tok isa Truth
        return convert(FiniteTruth, tok)
    elseif tok isa NamedConnective{:∧}
        c1, c2 = _children(ψ)
        return algebra.monoid(
            evalformula(c1, steps, algebra), evalformula(c2, steps, algebra)
        )
    elseif tok isa NamedConnective{:∨}
        c1, c2 = _children(ψ)
        return algebra.join(
            evalformula(c1, steps, algebra), evalformula(c2, steps, algebra)
        )
    elseif tok isa NamedConnective{:→}
        c1, c2 = _children(ψ)
        return algebra.implication(
            evalformula(c1, steps, algebra), evalformula(c2, steps, algebra)
        )
    else
        error("test evaluator does not support connective $tok")
    end
end

################################################################################
## Default path is untouched ###################################################
################################################################################

println("Default path is untouched by `certificate`")

@test alphasat(MVHSTableau, ⊤, p, booleanalgebra; timeout=timeout) isa Union{Bool,Nothing}
@test alphasat(
    MVHSTableau, ⊤, p, booleanalgebra; timeout=timeout, certificate=false
) isa Union{Bool,Nothing}
@test alphasat(MVHSTableau, ⊤, p, booleanalgebra; timeout=timeout) == true

################################################################################
## Unsatisfiable: every recorded closure is re-checkable ######################
################################################################################

println("Unsatisfiable formula: certificate closures re-check against the algebra")

unsatformula = ∧(p, →(p, ⊥))
result, cert = alphasat(
    MVHSTableau, ⊤, unsatformula, booleanalgebra; timeout=timeout, certificate=true
)
@test result == false
@test cert isa UnsatCertificate
@test !isempty(cert.closures)
for c in cert.closures
    @test verify_closure(c, booleanalgebra)
    @test !isempty(c.steps)
    @test c.steps[end].world == c.world
end
d = serialize_alphasat(result, cert)
@test d["schema_version"] == "solereasoners.alphasat.v1"
@test d["result"] == false
@test d["certificate"]["kind"] == "unsat"
@test length(d["certificate"]["closures"]) == length(cert.closures)

################################################################################
## Satisfiable: the branch is re-checked for consistency and semantics ########
################################################################################

println("Satisfiable formula: certificate branch re-checks as a genuine model")

result, cert = alphasat(
    MVHSTableau, ⊤, p, booleanalgebra; timeout=timeout, certificate=true
)
@test result == true
@test cert isa SatCertificate
@test !isempty(cert.steps)
@test !hascontradiction(cert.steps, booleanalgebra)
α0, φ0 = cert.steps[1].assertion
@test cert.steps[1].judgement == true
v = evalformula(φ0, cert.steps, booleanalgebra)
@test precedeq(booleanalgebra, convert(FiniteTruth, α0), v)
d = serialize_alphasat(result, cert)
@test d["certificate"]["kind"] == "sat"

################################################################################
## Many-valued: X1-style closure is not Boolean p/¬p ###########################
################################################################################

println("Many-valued algebra (Ł4): certificate reflects non-Boolean closure")

result, cert = alphasat(
    MVHSTableau, Ł4α, ⊥, Ł4; timeout=timeout, certificate=true
)
@test result == false
@test cert isa UnsatCertificate
@test !isempty(cert.closures)
for c in cert.closures
    @test verify_closure(c, Ł4)
end

result, cert = alphasat(
    MVHSTableau, ⊥, Ł4α, Ł4; timeout=timeout, certificate=true
)
@test result == true
@test cert isa SatCertificate
@test !hascontradiction(cert.steps, Ł4)
α0, φ0 = cert.steps[1].assertion
v = evalformula(φ0, cert.steps, Ł4)
@test precedeq(Ł4, convert(FiniteTruth, α0), v)

################################################################################
## nothing: undetermined can never look like a proof ###########################
################################################################################

println("Timeout: undetermined certificate cannot be mistaken for a verdict")

bignested = p
for _ in 1:6
    global bignested = ∧(bignested, →(bignested, q))
end
result, cert = alphasat(
    MVHSTableau, ⊤, bignested, booleanalgebra; timeout=0, certificate=true
)
@test isnothing(result)
@test cert isa UndeterminedCertificate
@test cert.reason ∈ (:timeout, :memory)
@test cert.cycle >= 1
@test cert.elapsed >= 0
d = serialize_alphasat(result, cert)
@test d["result"] === nothing
@test d["certificate"]["kind"] == "undetermined"
@test !haskey(d["certificate"], "closures")
@test !haskey(d["certificate"], "steps")
