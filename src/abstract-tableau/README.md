# Abstract Tableau

This folder contains the necessary components to reason about any logic using an
Analytic Tableaux Technique, suitable for both satisfiability and authomated
theorem proving.

All tableaux structures are recursive structures resembling a tree structure.
Each logic is associated with a specific tableau structure subtype of
`AbstractTableau`, and must comprise at least a `father`, an array of
`children`, and two flags `expanded` and `closed`.
