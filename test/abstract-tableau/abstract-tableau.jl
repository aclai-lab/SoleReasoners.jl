using SoleReasoners: AbstractTableau
using SoleReasoners: pushchild!, father, children, expanded, closed, isroot
using SoleReasoners: isleaf, expand!, close!, findexpansionnode, findleaves

################################################################################
# Constructor ##################################################################
################################################################################
mutable struct MyTableau <: AbstractTableau
    const father::Union{MyTableau, Nothing}
    const children::Vector{MyTableau}
    expanded::Bool
    closed::Bool

    MyTableau() = new(nothing, Vector{MyTableau}(), false, false)

    function MyTableau(father::MyTableau)
        newtableau = new(father, Vector{MyTableau}(), false, false)
        pushchild!(father, newtableau)
        return newtableau
    end
end

################################################################################
# Logger #######################################################################
################################################################################
t = MyTableau()
b = IOBuffer()
@test_throws ErrorException(
    "$(b)Please, provide a `show` method for MyTableau"
) show(b, t)

################################################################################
# Core operations ##############################################################
################################################################################
t0 = MyTableau()
t1 = MyTableau(t0)
t2 = MyTableau(t1)

@test isnothing(father(t0))
@test children(t0) == [t1]
@test !expanded(t0)
@test !closed(t0)
@test isroot(t0)
@test !isleaf(t0)

@test father(t1) == t0
@test children(t1) == [t2]
@test !expanded(t1)
@test !closed(t1)
@test !isroot(t1)
@test !isleaf(t1)

@test father(t2) == t1
@test isempty(children(t2))
@test !expanded(t2)
@test !closed(t2)
@test !isroot(t2)
@test isleaf(t2)

@test findexpansionnode(t2) == t0
expand!(t0)
@test expanded(t0) == true
@test expanded(t1) == false
@test expanded(t2) == false
@test findexpansionnode(t2) == t1
expand!(t1)
@test expanded(t0) == true
@test expanded(t1) == true
@test expanded(t2) == false
@test findexpansionnode(t2) == t2

@test findleaves(t0) == [t2]
@test findleaves(t1) == [t2]
@test findleaves(t2) == [t2]

close!(t1)
@test closed(t0) == true
@test closed(t1) == true
@test closed(t2) == true

t0 = MyTableau()
t1 = MyTableau(t0)
t2 = MyTableau(t0)

@test isnothing(father(t0))
@test children(t0) == [t1, t2]
@test !expanded(t0)
@test !closed(t0)
@test isroot(t0)
@test !isleaf(t0)

@test father(t1) == t0
@test isempty(children(t1))
@test !expanded(t1)
@test !closed(t1)
@test !isroot(t1)
@test isleaf(t1)

@test father(t2) == t0
@test isempty(children(t2))
@test !expanded(t2)
@test !closed(t2)
@test !isroot(t2)
@test isleaf(t2)

@test findexpansionnode(t1) == t0
@test findexpansionnode(t2) == t0
expand!(t0)
@test expanded(t0) == true
@test expanded(t1) == false
@test expanded(t2) == false
@test findexpansionnode(t1) == t1
@test findexpansionnode(t2) == t2

@test findleaves(t0) == [t1, t2]
@test findleaves(t1) == [t1]
@test findleaves(t2) == [t2]

close!(t1)
@test closed(t0) == false
@test closed(t1) == true
@test closed(t2) == false
close!(t2)
@test closed(t0) == true
@test closed(t1) == true
@test closed(t2) == true

ts = Vector{MyTableau}()
push!(ts, MyTableau())
for i in 1:10000
    push!(ts, MyTableau(last(ts)))
end
l1 = MyTableau(last(ts))
l2 = MyTableau(last(ts))
l3 = MyTableau(last(ts))

@test findleaves(first(ts)) == [l1, l2, l3]

t0 = MyTableau()
t1 = MyTableau(t0)
t2 = MyTableau(t0)
t3 = MyTableau(t2)
t4 = MyTableau(t2)

@test findleaves(t0) == [t1, t3, t4]
