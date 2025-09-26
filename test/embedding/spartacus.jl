using SoleReasoners: installspartacus, ssat, sunsat, sval, sunval

installspartacus()

k = parseformula("□(p→q)→(□p→□q)")
n = parseformula("◊p∧□¬p")

@test ssat(k)
@test !sunsat(k)
@test sval(k)
@test !sunval(k)
@test !ssat(n)
@test sunsat(n)
@test !sval(n)
@test sunval(n)
