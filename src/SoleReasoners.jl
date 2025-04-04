module SoleReasoners

import Base: isempty, push!, Base.pop!, Order.lt
using DataStructures
using Random
using Reexport
using Base.Threads
using StatsBase

# @reexport using SoleLogics

# include("core.jl")

# export naivechoosenode, roundrobin, sat

# using SoleLogics.ManyValuedLogics
# using SoleLogics.ManyValuedLogics: FiniteTruth, FiniteAlgebra
# using SoleLogics.ManyValuedLogics: lesservalues, maximalmembers, minimalmembers

# include("many-valued-tableau.jl")
# export alphasat, prove, alphaprove

include("many-valued-multi-modal-logic/many-valued-multi-modal-logic.jl")
include("many-valued-multi-modal-tableau/many-valued-multi-modal-tableau.jl")
include("many-valued-multi-modal-tableau/mvltlfp-tableau.jl")
include("many-valued-multi-modal-tableau/mvcl-tableau.jl")
include("many-valued-multi-modal-tableau/mvhs-tableau.jl")
include("many-valued-multi-modal-tableau/mvlrcc8-tableau.jl")

# include("mvhs.jl")
# export mvhsalphasat, mvhsalphaprove

# include("hybrid-tableau.jl")
# export hybridalphasat, hybridalphaprove

# include("hybrid-modal-tableau.jl")
# export hybridmvhsalphasat, hybridmvhsalphaprove

# include("utils.jl")

# export dimacstosole, booleantofuzzy

end # module SoleReasoners
