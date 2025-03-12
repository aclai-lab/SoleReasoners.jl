using SoleLogics: isbot, istop
using SoleLogics.ManyValuedLogics: FiniteFLewAlgebra, FiniteTruth, succeedeq
using StaticArrays: SMatrix

"""
Check if a domain of cardinality `N` enriched with two functions `mveq` and
`mvlt` form a many-valued linear order, i.e., if the following axioms are
satisfied:
1. ̃=(x,y) = ⊤ iff x = y
2. ̃=(x,y) = ̃=(y,x)
3. ̃<(x,x) = ⊥
4. ̃<(x,z) ⪰ ̃<(x,y) ⋅ ̃<(y,z)
5. if ̃<(x,y) ≻ 0 and ̃<(y,z) ≻ 0 then ̃<(x,z) ≻ 0
6. if ̃<(x,y) = 0 and ̃<(y,x) = 0 then ̃=(x,y) = 1
7. if ̃=(x,y) ≻ 0 then ̃<(x,y) ≺ 1
"""
function isaManyValuedLinearOrder(
    mvlt::M,
    mveq::M,
    algebra::FiniteFLewAlgebra
) where {
    N,
    M<:SMatrix{N,N,FiniteTruth}
}
    for x ∈ UInt8(1):UInt8(N)
        if !istop(mveq[x,x])
            error("(D,̃<,̃=) is not a many-valued linear order (1)")
        end
        if !isbot(mvlt[x,x])
            error("(D,̃<,̃=) is not a many-valued linear order (3)")
        end
        for y ∈ UInt8(1):UInt8(N)
            if istop(mveq[x,y]) && x != y
                error("(D,̃<,̃=) is not a many-valued linear order (1)")
            end
            if mveq[x,y] != mveq[y,x]
                error("(D,̃<,̃=) is not a many-valued linear order (2)")
            end
            if isbot(mvlt[x,y]) && isbot(mvlt[y,x]) && !istop(mveq[x,y])
                error("(D,̃<,̃=) is not a many-valued linear order (6)")
            end
            if !isbot(mveq[x,y]) && istop(mvlt[x,y])
                error("(D,̃<,̃=) is not a many-valued linear order (7)")
            end
            for z ∈ UInt8(1):UInt8(N)
                if !succeedeq(
                    algebra,
                    mvlt[x,z],
                    algebra.monoid(mvlt[x,y], mvlt[y,z])
                )
                    error("(D,̃<,̃=) is not a many-valued linear order (4)")
                end
                if !isbot(mvlt[x,y]) && !isbot(mvlt[y,z]) && isbot(mvlt[x,z])
                    error("(D,̃<,̃=) is not a many-valued linear order (5)")
                end
            end
        end
    end
end

"""
    struct ManyValuedLinearOrder{N, M<:SMatrix{N,N,FiniteTruth}}
        mvlt::M # ̃<
        mveq::M # ̃=
        algebra::FiniteFLewAlgebra
    end

Given an `algebra`, a many-valued linear order is a structure of the type
(D,̃<,̃=) where D is a domain enriched with two functions ̃<, ̃=: D×D→A, for which
the following conditions apply for every x, y and z in the domain D:
1. ̃=(x,y) = ⊤ iff x = y
2. ̃=(x,y) = ̃=(y,x)
3. ̃<(x,x) = ⊥
4. ̃<(x,z) ⪰ ̃<(x,y) ⋅ ̃<(y,z)
5. if ̃<(x,y) ≻ 0 and ̃<(y,z) ≻ 0 then ̃<(x,z) ≻ 0
6. if ̃<(x,y) = 0 and ̃<(y,x) = 0 then ̃=(x,y) = 1
7. if ̃=(x,y) ≻ 0 then ̃<(x,y) ≺ 1
"""
struct ManyValuedLinearOrder{M<:SMatrix}
    mvlt::M # ̃<
    mveq::M # ̃=
    algebra::FiniteFLewAlgebra

    function ManyValuedLinearOrder(
        mvlt::M,
        mveq::M,
        algebra::FiniteFLewAlgebra
    ) where {
        N,
        M<:SMatrix{N,N,FiniteTruth}
    }
        isaManyValuedLinearOrder(mvlt, mveq, algebra)
        new{M}(mvlt, mveq, algebra)
    end
end
