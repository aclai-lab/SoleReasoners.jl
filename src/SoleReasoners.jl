module SoleReasoners

import Base: isempty, push!, Base.pop!, Order.lt
using DataStructures
using Random
using Reexport
using StatsBase

@reexport using SoleLogics

include("core.jl")

export Tableau, φ, literals, naivechooseleaf, roundrobin, sat

include("fuzzy.jl")

export FuzzyTableau, SignedFormula, fuzzysat, prove

include("utils.jl")

export dimacstosole, booleantofuzzy

end # module SoleReasoners
