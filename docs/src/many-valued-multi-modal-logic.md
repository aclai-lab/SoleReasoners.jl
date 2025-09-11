```@meta
CurrentModule = SoleReasoners
```

```@contents
Pages = ["many-valued-multi-modal-logic.md"]
```

# [Many-Valued Multi-Modal Logic](@id man-core)

For all logics, many-valuedness is treated through $FL_{ew}$-algebras.

## Many-Valued Linear Order

All logics are defined over a many-valued linear order.

```@docs
isaManyValuedLinearOrder(
    mvlt::M,
    mveq::M,
    algebra::FiniteFLewAlgebra
) where {
    N,
    M<:SMatrix{N,N,FiniteTruth}
}
checkManyValuedLinearOrder(
    mvlt::M,
    mveq::M,
    algebra::FiniteFLewAlgebra
) where {
    N,
    M<:SMatrix{N,N,FiniteTruth}
}
ManyValuedLinearOrder
cardinality(o::ManyValuedLinearOrder)
Base.show(io::IO, o::ManyValuedLinearOrder)
```

## Many-Valued Multi-Modal Logic

Each logic requires the definition of:
 - a data structure representing a world in a specific logic
 - the many-valued evaluation functions for the relations in the logic

One should notice how these structures change from the ones in `SoleLogics.jl`,
as in the latter worlds need to carry a specific value that will be used for
evaluation purposes (e.g., `check` and learning), hence they are not suited for
reasoning tasks (e.g., frames should be dynamic).

### Many-Valued Linear Temporal Logic with Future and Past

```@docs
Point1D
Base.show(io::IO, p::Point1D)
mvlt(x1::Point1D, x2::Point1D, o::ManyValuedLinearOrder)
mveq(x1::Point1D, x2::Point1D, o::ManyValuedLinearOrder)
mvleq(x1::Point1D, x2::Point1D, o::ManyValuedLinearOrder)
mveval(::typeof(LTLFP_F), x1::Point1D, x2::Point1D, o::ManyValuedLinearOrder)
mveval(::typeof(LTLFP_P), x1::Point1D, x2::Point1D, o::ManyValuedLinearOrder)
```

### Many-Valued Compass Logic

```@docs
Point2D
Base.show(io::IO, p::Point2D)
mveval(
    ::typeof(CL_N),
    p1::Point2D,
    p2::Point2D,
    (ox,oy)::NTuple{2,ManyValuedLinearOrder}
)
mveval(
    ::typeof(CL_S),
    p1::Point2D,
    p2::Point2D,
    (ox,oy)::NTuple{2,ManyValuedLinearOrder}
)
mveval(
    ::typeof(CL_E),
    p1::Point2D,
    p2::Point2D,
    (ox,oy)::NTuple{2,ManyValuedLinearOrder}
)
mveval(
    ::typeof(CL_W),
    p1::Point2D,
    p2::Point2D,
    (ox,oy)::NTuple{2,ManyValuedLinearOrder}
)
```

### Many-Valued Halpern and Shoham's modal logic of time intervals

```@docs
isaInterval(p1::Point1D, p2::Point1D, o::ManyValuedLinearOrder)
checkInterval(p1::Point1D, p2::Point1D, o::ManyValuedLinearOrder)
Interval
Base.show(io::IO, i::Interval)
mveval(
    ::typeof(HS_A),
    i1::Interval,
    i2::Interval,
    o::ManyValuedLinearOrder
)
mveval(
    ::typeof(HS_L),
    i1::Interval,
    i2::Interval,
    o::ManyValuedLinearOrder
)
mveval(
    ::typeof(HS_B),
    i1::Interval,
    i2::Interval,
    o::ManyValuedLinearOrder
)
mveval(
    ::typeof(HS_E),
    i1::Interval,
    i2::Interval,
    o::ManyValuedLinearOrder
)
mveval(
    ::typeof(HS_D),
    i1::Interval,
    i2::Interval,
    o::ManyValuedLinearOrder
)
mveval(
    ::typeof(HS_O),
    i1::Interval,
    i2::Interval,
    o::ManyValuedLinearOrder
)
mveval(
    ::typeof(HS_Ai),
    i1::Interval,
    i2::Interval,
    o::ManyValuedLinearOrder
)
mveval(
    ::typeof(HS_Li),
    i1::Interval,
    i2::Interval,
    o::ManyValuedLinearOrder
)
mveval(
    ::typeof(HS_Bi),
    i1::Interval,
    i2::Interval,
    o::ManyValuedLinearOrder
)
mveval(
    ::typeof(HS_Ei),
    i1::Interval,
    i2::Interval,
    o::ManyValuedLinearOrder
)
mveval(
    ::typeof(HS_Di),
    i1::Interval,
    i2::Interval,
    o::ManyValuedLinearOrder
)
mveval(
    ::typeof(HS_Oi),
    i1::Interval,
    i2::Interval,
    o::ManyValuedLinearOrder
)
```

### Many-Valued Lutz and Wolter's modal logic of topological relations with rectangular areas aligned with the axes

```@docs
Rectangle
Base.show(io::IO, r::Rectangle)
mveval(
    ::typeof(LRCC8_Rec_DC),
    r1::Rectangle,
    r2::Rectangle,
    (ox,oy)::NTuple{2,ManyValuedLinearOrder}
)
mveval(
    ::typeof(LRCC8_Rec_EC),
    r1::Rectangle,
    r2::Rectangle,
    (ox,oy)::NTuple{2,ManyValuedLinearOrder}
)
mveval(
    ::typeof(LRCC8_Rec_PO),
    r1::Rectangle,
    r2::Rectangle,
    (ox,oy)::NTuple{2,ManyValuedLinearOrder}
)
mveval(
    ::typeof(LRCC8_Rec_TPP),
    r1::Rectangle,
    r2::Rectangle,
    (ox,oy)::NTuple{2,ManyValuedLinearOrder}
)
mveval(
    ::typeof(LRCC8_Rec_NTPP),
    r1::Rectangle,
    r2::Rectangle,
    (ox,oy)::NTuple{2,ManyValuedLinearOrder}
)
mveval(
    ::typeof(LRCC8_Rec_TPPi),
    r1::Rectangle,
    r2::Rectangle,
    (ox,oy)::NTuple{2,ManyValuedLinearOrder}
)
mveval(
    ::typeof(LRCC8_Rec_NTPPi),
    r1::Rectangle,
    r2::Rectangle,
    (ox,oy)::NTuple{2,ManyValuedLinearOrder}
)
```
