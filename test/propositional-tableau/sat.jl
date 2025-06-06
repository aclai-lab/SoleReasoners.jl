@test sat(parseformula("⊥"))        == false
@test sat(parseformula("⊤"))        == true
@test sat(parseformula("¬⊥"))       == true
@test sat(parseformula("¬⊤"))       == false
@test sat(parseformula("⊥∧⊥"))      == false
@test sat(parseformula("⊥∧⊤"))      == false
@test sat(parseformula("⊤∧⊥"))      == false
@test sat(parseformula("⊤∧⊤"))      == true
@test sat(parseformula("⊥∨⊥"))      == false
@test sat(parseformula("⊥∨⊤"))      == true
@test sat(parseformula("⊤∨⊥"))      == true
@test sat(parseformula("⊤∨⊤"))      == true
@test sat(parseformula("⊥→⊥"))      == true
@test sat(parseformula("⊥→⊤"))      == true
@test sat(parseformula("⊤→⊥"))      == false
@test sat(parseformula("⊤→⊤"))      == true

@test sat(parseformula("¬(⊥)"))     == true
@test sat(parseformula("¬(⊤)"))     == false
@test sat(parseformula("¬(¬⊥)"))    == false
@test sat(parseformula("¬(¬⊤)"))    == true
@test sat(parseformula("¬(⊥∧⊥)"))   == true
@test sat(parseformula("¬(⊥∧⊤)"))   == true
@test sat(parseformula("¬(⊤∧⊥)"))   == true
@test sat(parseformula("¬(⊤∧⊤)"))   == false
@test sat(parseformula("¬(⊥∨⊥)"))   == true
@test sat(parseformula("¬(⊥∨⊤)"))   == false
@test sat(parseformula("¬(⊤∨⊥)"))   == false
@test sat(parseformula("¬(⊤∨⊤)"))   == false
@test sat(parseformula("¬(⊥→⊥)"))   == false
@test sat(parseformula("¬(⊥→⊤)"))   == false
@test sat(parseformula("¬(⊤→⊥)"))   == true
@test sat(parseformula("¬(⊤→⊤)"))   == false

@test sat(parseformula("p"))        == true
@test sat(parseformula("¬p"))       == true
@test sat(parseformula("p∧p"))      == true
@test sat(parseformula("p∧¬p"))     == false
@test sat(parseformula("¬p∧p"))     == false
@test sat(parseformula("¬p∧¬p"))    == true
@test sat(parseformula("p∨p"))      == true
@test sat(parseformula("p∨¬p"))     == true
@test sat(parseformula("¬p∨p"))     == true
@test sat(parseformula("¬p∨¬p"))    == true
@test sat(parseformula("p→p"))      == true
@test sat(parseformula("p→¬p"))     == true
@test sat(parseformula("¬p→p"))     == true
@test sat(parseformula("¬p→¬p"))    == true

@test sat(parseformula("¬¬p"))      == true
@test sat(parseformula("¬(p∧p)"))   == true
@test sat(parseformula("¬(p∧¬p)"))  == true
@test sat(parseformula("¬(¬p∧p)"))  == true
@test sat(parseformula("¬(¬p∧¬p)")) == true
@test sat(parseformula("¬(p∨p)"))   == true
@test sat(parseformula("¬(p∨¬p)"))  == false
@test sat(parseformula("¬(¬p∨p)"))  == false
@test sat(parseformula("¬(¬p∨¬p)")) == true
@test sat(parseformula("¬(p→p)"))   == false
@test sat(parseformula("¬(p→¬p)"))  == true
@test sat(parseformula("¬(¬p→p)"))  == true
@test sat(parseformula("¬(¬p→¬p)")) == false

@test sat(parseformula(
    "(x∨y∨z)∧(x∨y∨¬z)∧(x∨¬y∨z)∧(x∨¬y∨¬z)∧(¬x∨y∨z)∧(¬x∨y∨¬z)∧(¬x∨¬y∨z)∧(¬x∨¬y∨¬z)"
)) == false

@test sat(
    dimacstosole("propositional-tableau/benchmark/sat/uf50-01.cnf")
) == true

@test sat(
    dimacstosole("propositional-tableau/benchmark/sat/uf50-02.cnf")
) == true

p = Atom("p")

# Define a new logical operator `⊕`
import SoleLogics: arity
const ⊕ = SoleLogics.NamedConnective{:⊕}()
SoleLogics.arity(::typeof(⊕)) = 2

# Give XOR semantics to the operator `⊕`
import SoleLogics: collatetruth
function SoleLogics.collatetruth(::typeof(⊕), (t1, t2)::NTuple{2,BooleanTruth})
    return Base.xor(istop(t1), istop(t2)) ? TOP : BOT
end

@test_throws ErrorException(
    "Error: unrecognized NamedConnective "
) sat(parseformula("¬p ∧ q") ⊕ p)
