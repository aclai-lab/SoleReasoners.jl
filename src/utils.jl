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
