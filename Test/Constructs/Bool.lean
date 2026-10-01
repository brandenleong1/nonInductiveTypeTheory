import Constructs.Bool
import Test.Util

namespace NonInductiveTypeTheory


-- Not
example : Bool.Not.{0} Bool.True  = Bool.False := rfl
example : Bool.Not.{0} Bool.False = Bool.True  := rfl

-- And
example : Bool.And.{0} Bool.True  Bool.True  = Bool.True  := rfl
example : Bool.And.{0} Bool.True  Bool.False = Bool.False := rfl
example : Bool.And.{0} Bool.False Bool.True  = Bool.False := rfl
example : Bool.And.{0} Bool.False Bool.False = Bool.False := rfl

-- Or
example : Bool.Or.{0} Bool.True  Bool.True  = Bool.True  := rfl
example : Bool.Or.{0} Bool.True  Bool.False = Bool.True  := rfl
example : Bool.Or.{0} Bool.False Bool.True  = Bool.True  := rfl
example : Bool.Or.{0} Bool.False Bool.False = Bool.False := rfl

-- Xor
example : Bool.Xor.{0} Bool.True  Bool.True  = Bool.False := rfl
example : Bool.Xor.{0} Bool.True  Bool.False = Bool.True  := rfl
example : Bool.Xor.{0} Bool.False Bool.True  = Bool.True  := rfl
example : Bool.Xor.{0} Bool.False Bool.False = Bool.False := rfl

-- Implies
example : Bool.Implies.{0} Bool.True  Bool.True  = Bool.True  := rfl
example : Bool.Implies.{0} Bool.True  Bool.False = Bool.False := rfl
example : Bool.Implies.{0} Bool.False Bool.True  = Bool.True  := rfl
example : Bool.Implies.{0} Bool.False Bool.False = Bool.True  := rfl

-- ¬(a ∧ b) = ¬a ∨ ¬b
example : Bool.Not.{0} (Bool.And Bool.True  Bool.True ) = Bool.Or (Bool.Not Bool.True ) (Bool.Not Bool.True ) := rfl
example : Bool.Not.{0} (Bool.And Bool.True  Bool.False) = Bool.Or (Bool.Not Bool.True ) (Bool.Not Bool.False) := rfl
example : Bool.Not.{0} (Bool.And Bool.False Bool.True ) = Bool.Or (Bool.Not Bool.False) (Bool.Not Bool.True ) := rfl
example : Bool.Not.{0} (Bool.And Bool.False Bool.False) = Bool.Or (Bool.Not Bool.False) (Bool.Not Bool.False) := rfl

-- Not is an involution
example : Bool.Not.{0} (Bool.Not Bool.True)  = Bool.True  := rfl
example : Bool.Not.{0} (Bool.Not Bool.False) = Bool.False := rfl

-- Implies a b = Or (Not a) b
example : Bool.Implies.{0} Bool.True  Bool.False = Bool.Or (Bool.Not Bool.True)  Bool.False := rfl
example : Bool.Implies.{0} Bool.False Bool.False = Bool.Or (Bool.Not Bool.False) Bool.False := rfl


end NonInductiveTypeTheory
