```@meta
CurrentModule = SoleReasoners
```

```@contents
Pages = ["abstract-tableau.md"]
```

# [Abstract Tableau](@id man-core)

All tableaux structures are recursive structures resembling a tree structure.
Each logic is associated with a specific tableau structure subtype of
`AbstractTableau`, and must comprise at least a `father`, an array of
`children`, and two flags `expanded` and `closed`.

```@docs
AbstractTableau
father(t::T) where {T<:AbstractTableau}
children(t::T) where {T<:AbstractTableau}
expanded(t::T) where {T<:AbstractTableau}
closed(t::T) where {T<:AbstractTableau}
isroot(t::T) where {T<:AbstractTableau}
isleaf(t::T) where {T<:AbstractTableau}
expand!(t::T) where {T<:AbstractTableau}
findexpansionnode(t::T) where {T<:AbstractTableau}
findleaves(leaves::Vector{T}, t::T) where {T<:AbstractTableau}
close!(t::T) where {T<:AbstractTableau}
pushchild!(father::T, child::T) where {T<:AbstractTableau}
Base.show(io::IO, _::T) where {T<:AbstractTableau}
```
