############################################################################################
#### Utils #################################################################################
############################################################################################

"""
    dimacstosole(dimacscnf::String)::Formula

Simple parsing from DIMACS CNF format to a SoleLogics Formula.

`dimacscnf` is the path of the file containing the formula in DIMACS CNF format.

TODO: cnftodimacs.
"""
function dimacstosole(dimacscnf::String)::Formula
    disjunctions = Set{Formula}()
    for line in readlines(dimacscnf)
        if !startswith(line, "c") && !startswith(line, "p") && !startswith(line, "%") && !startswith(line, "0") && line != ""
            words = split(line)
            literals = Set{Formula}()
            for word ∈ words
                if word != "0"
                    if startswith(word, "-")
                        literal = ¬Atom(abs(parse(Int, word)))
                    else
                        literal = Atom(abs(parse(Int, word)))
                    end
                    push!(literals, literal)
                end
            end
            push!(disjunctions, ∨(literals...))
        end
    end
    return ∧(disjunctions...)
end

"""
Util function to convert a boolean formula to fuzzy format, i.e.,
replacing each negation ¬X with the implication X → ⊥.
"""
function booleantofuzzy(φ::Formula)
    if token(φ) isa Union{Atom, BooleanTruth}
        return φ
    elseif token(φ) isa NamedConnective{:¬}
        return →(booleantofuzzy(children(φ)[1]),⊥)
    else
        (a, b) = children(φ)
        return token(φ)(booleantofuzzy(a), booleantofuzzy(b))
    end
end
