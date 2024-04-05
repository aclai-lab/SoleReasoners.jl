module SoleReasoners

import Base: isempty, push!, Base.pop!, Order.lt
using DataStructures
using Random
using Reexport
using StatsBase

@reexport using SoleLogics

top = SoleLogics.top

include("core.jl")

export naivechooseleaf, roundrobin, sat

using SoleLogics.ManyValuedLogics
using SoleLogics.ManyValuedLogics: FiniteTruth, FiniteAlgebra
using SoleLogics.ManyValuedLogics: lesservalues, maximalmembers, minimalmembers

include("many-valued-tableau.jl")

export alphasat, prove, alphaprove

include("utils.jl")

export dimacstosole, booleantofuzzy

end # module SoleReasoners
