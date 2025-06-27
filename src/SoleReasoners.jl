module SoleReasoners

include("abstract-tableau/abstract-tableau.jl")
include("metric-heap/metric-heap.jl")
include("propositional-tableau/propositional-tableau.jl")
export sat
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
include("metric-heap/metrics.jl")
export randombranch, distancefromroot, inversedistancefromroot, formulaheight
include("metric-heap/choose-node.jl")
export roundrobin!, mostvoted!
include("utils/utils.jl")
export booleantofuzzy, dimacstosole

end # module SoleReasoners
