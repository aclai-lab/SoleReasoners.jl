module SoleReasoners

import Base: isempty, push!, Base.pop!, Order.lt
using DataStructures
using Random
using Reexport
using StatsBase

@reexport using SoleLogics

include("core.jl")

export AbstractTableau, Tableau, φ, literals, naivechooseleaf, roundrobin, sat

include("fuzzy.jl")

export FuzzyTableau, SignedFormula, signedformula, height, fuzzysat, prove, alphasat

include("utils.jl")

export dimacstosole, booleantofuzzy

end # module SoleReasoners
