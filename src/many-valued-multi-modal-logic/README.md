# Many-Valued Multi-Modal Logic

This folder contains the necessary components to reason about many-valued
multi-modal logic, such as the definition of a many-valued linear order
([many-valued-linear-order.jl](many-valued-linear-order.jl)).
Each file contains the definition of:
 - a data structure representing a world in a specific logic
 - the many-valued evaluation functions for the relations in the logic

One should notice how these structures change from the ones in `SoleLogics.jl`,
as in the latter worlds need to carry a specific value that will be used for
evaluation purposes (e.g., `check` and learning), hence they are not suited for
reasoning tasks (e.g., frames should be dynamic).

Currently supported logics are:
 - Many-Valued Linear Temporal Logic with Future and Past:
 [mvltlfp.jl](mvltlfp.jl)
 - Many-Valued Compass Logic: [mvcs.jl](mvcs.jl)
 - Many-Valued Halpern and Shoham's modal logic of time intervals:
 [mvhs.jl](mvhs.jl)
 - Many-Valued Lutz and Wolter's modal logic of topological relations with
 rectangular areas aligned with the axes: [mvlrcc8.jl](mvlrcc8.jl)

For all logics, many-valuedness is treated through $FL_{ew}$-algebras.
