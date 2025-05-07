module SoleReasoners

# import Base: isempty, push!, Base.pop!, Order.lt
# using DataStructures
# using Random
# using Reexport
# using Base.Threads
# using StatsBase

# @reexport using SoleLogics

# include("core.jl")

# export naivechoosenode, roundrobin, sat

# using SoleLogics.ManyValuedLogics
# using SoleLogics.ManyValuedLogics: FiniteTruth, FiniteAlgebra
# using SoleLogics.ManyValuedLogics: lesservalues, maximalmembers, minimalmembers

# include("many-valued-tableau.jl")
# export alphasat, prove, alphaprove

include("abstract-tableau/abstract-tableau.jl")
include("metric-heap/metric-heap.jl")
include("metric-heap/metrics.jl")
export randombranch, distancefromroot, inversedistancefromroot
include("metric-heap/choose-node.jl")
export roundrobin!, mostvoted!
include("many-valued-multi-modal-logic/many-valued-multi-modal-logic.jl")
include("many-valued-multi-modal-tableau/many-valued-multi-modal-tableau.jl")
include("many-valued-multi-modal-tableau/alphasat.jl")
export alphasat, alphaval
include("many-valued-multi-modal-tableau/mvltlfp-tableau.jl")
export MVLTLFPTableau
include("many-valued-multi-modal-tableau/mvcl-tableau.jl")
export MVCLTableau
include("many-valued-multi-modal-tableau/mvhs-tableau.jl")
export MVHSTableau
include("many-valued-multi-modal-tableau/mvlrcc8-tableau.jl")
export MVLRCC8Tableau
include("utils.jl")
export booleantofuzzy

# include("mvhs.jl")
# export mvhsalphasat, mvhsalphaprove

# include("hybrid-tableau.jl")
# export hybridalphasat, hybridalphaprove

# include("hybrid-modal-tableau.jl")
# export hybridmvhsalphasat, hybridmvhsalphaprove

# include("utils.jl")

# export dimacstosole, booleantofuzzy

end # module SoleReasoners
