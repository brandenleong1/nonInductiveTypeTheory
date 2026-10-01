import Constructs.Bool

namespace NonInductiveTypeTheory

namespace BoolTest


-- Computation on Bool
example : Bool.Not.{0}      Bool.True  = Bool.False := rfl
example : Bool.Not.{0}      Bool.False = Bool.True  := rfl

example : Bool.And.{0}      Bool.True  Bool.False = Bool.False := rfl
example : Bool.Or.{0}       Bool.False Bool.True  = Bool.True  := rfl
example : Bool.Xor.{0}      Bool.True  Bool.True  = Bool.False := rfl
example : Bool.Implies.{0}  Bool.True  Bool.False = Bool.False := rfl

-- Bool Laws
example (b : Bool.{0}) :
  Bool.Not (Bool.Not b) = b := rfl

example (a : Bool.{0}) (b : Bool.{0}) :
  Bool.Not (Bool.And a b) =
    Bool.Or (Bool.Not a) (Bool.Not b) := rfl

example (a : Bool.{0}) (b : Bool.{0}) :
  Bool.Not (Bool.Or a b) =
    Bool.And (Bool.Not a) (Bool.Not b) := rfl

example (a : Bool.{0}) (b : Bool.{0}) :
  Bool.Implies a b = Bool.Or (Bool.Not a) b := rfl

-- Identity + Absorbing Laws
example (b : Bool.{0}) : Bool.And Bool.True b = b := rfl
example (b : Bool.{0}) : Bool.And b Bool.True = b := rfl
example (b : Bool.{0}) : Bool.And Bool.False b = Bool.False := rfl

example (b : Bool.{0}) : Bool.Or Bool.False b = b := rfl
example (b : Bool.{0}) : Bool.Or b Bool.False = b := rfl
example (b : Bool.{0}) : Bool.Or Bool.True b = Bool.True := rfl

example (b : Bool.{0}) : Bool.Xor Bool.False b = b := rfl
example (b : Bool.{0}) : Bool.Xor b Bool.False = b := rfl
example (b : Bool.{0}) : Bool.Xor Bool.True b = Bool.Not b := rfl
example (b : Bool.{0}) : Bool.Xor b Bool.True = Bool.Not b := rfl

-- Associativity
example (a : Bool.{0}) (b : Bool.{0}) (c : Bool.{0}) :
  Bool.And (Bool.And a b) c = Bool.And a (Bool.And b c) := rfl

example (a : Bool.{0}) (b : Bool.{0}) (c : Bool.{0}) :
  Bool.Or (Bool.Or a b) c = Bool.Or a (Bool.Or b c) := rfl


end BoolTest

end NonInductiveTypeTheory
