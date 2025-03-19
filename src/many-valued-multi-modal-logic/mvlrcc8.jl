using SoleLogics: LRCC8_Rec_DC, LRCC8_Rec_EC, LRCC8_Rec_PO
using SoleLogics: LRCC8_Rec_TPP, LRCC8_Rec_TPPi, LRCC8_Rec_NTPP, LRCC8_Rec_NTPPi

"""
    struct Rectangle
        ix::Interval
        iy::Interval
    end

A `Rectangle` is represented by an `Interval` on a many-valued linear order `Dx`
and another `Interval` on a many-valued linear order `Dy`.
"""
struct Rectangle
    ix::Interval
    iy::Interval
end

"""
A `Rectangle` is printed as `([xi,xj],[yk,yl])`, where `i` and `j` are the
indexes of the `Point1D`s of the first `Interval` in the domain associated with
the many-valued linear order `Dx` and `k` and `l` are the indexes of the
`Point1D`s of the second `Interval` in the domain associated with the
many-valued linear order `Dy`.
"""
function Base.show(io::IO, r::Rectangle)
    print(
        io,
        "(" *
            "[x$(r.ix.p1.index),x$(r.ix.p2.index)]," *
            "[y$(r.iy.p1.index),y$(r.iy.p2.index)]" *
        ")"
    )
end

"""
    function mveval(
        ::typeof(LRCC8_Rec_DC),
        r1::Rectangle,
        r2::Rectangle,
        (ox,oy)::NTuple{2,ManyValuedLinearOrder}
    )
Many-valued evaluation function r1Rr2 for relation R=LRCC8_Rec_DC in many-valued
linear orders `ox` and `oy` (how much `r2` is disconnected from `r1`).
"""
function mveval(
    ::typeof(LRCC8_Rec_DC),
    r1::Rectangle,
    r2::Rectangle,
    (ox,oy)::NTuple{2,ManyValuedLinearOrder}
)
    return ox.algebra.join(
        ox.algebra.join(
            mvlt(r1.ix.p2, r2.ix.p1, ox),
            mvlt(r1.iy.p2, r2.iy.p1, oy)
        ),
        ox.algebra.join(
            mvlt(r2.ix.p2, r1.ix.p1, ox),
            mvlt(r2.iy.p2, r1.iy.p1, oy)
        )
    )
end

"""
    function mveval(
        ::typeof(LRCC8_Rec_EC),
        r1::Rectangle,
        r2::Rectangle,
        (ox,oy)::NTuple{2,ManyValuedLinearOrder}
    )
Many-valued evaluation function r1Rr2 for relation R=LRCC8_Rec_EC in many-valued
linear orders `ox` and `oy` (how much `r2` is externally connected with `r1`).
"""
function mveval(
    ::typeof(LRCC8_Rec_EC),
    r1::Rectangle,
    r2::Rectangle,
    (ox,oy)::NTuple{2,ManyValuedLinearOrder}
)
    return ox.algebra.join(
        ox.algebra.monoid(
            ox.algebra.join(
                mveq(r1.ix.p1, r2.ix.p2, ox),
                mveq(r1.ix.p2, r2.ix.p1, ox)
            ),
            ox.algebra.join(
                ox.algebra.monoid(
                    mvleq(r1.iy.p1, r2.iy.p1, oy),
                    mvleq(r2.iy.p1, r1.iy.p2, oy)
                ),
                ox.algebra.monoid(
                    mvleq(r2.iy.p1, r1.iy.p1, oy),
                    mvleq(r1.iy.p1, r2.iy.p2, oy)
                )
            )
        ),
        ox.algebra.monoid(
            ox.algebra.join(
                mveq(r1.iy.p1, r2.iy.p2, oy),
                mveq(r1.iy.p2, r2.iy.p1, oy)
            ),
            ox.algebra.join(
                ox.algebra.monoid(
                    mvleq(r1.ix.p1, r2.ix.p1, ox),
                    mvleq(r2.ix.p1, r1.ix.p2, ox)
                ),
                ox.algebra.monoid(
                    mvleq(r2.ix.p1, r1.ix.p1, ox),
                    mvleq(r1.ix.p1, r2.ix.p2, ox)
                )
            )
        )
    )
end
