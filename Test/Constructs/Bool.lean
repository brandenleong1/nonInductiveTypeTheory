import Constructs.Bool

namespace NonInductiveTypeTheory

namespace BoolTest


-- Computation on Bool
example : Bool.not.{0}      Bool.True  = Bool.False := rfl
example : Bool.not.{0}      Bool.False = Bool.True  := rfl

example : Bool.and.{0}      Bool.True  Bool.False = Bool.False := rfl
example : Bool.or.{0}       Bool.False Bool.True  = Bool.True  := rfl
example : Bool.xor.{0}      Bool.True  Bool.True  = Bool.False := rfl
example : Bool.implies.{0}  Bool.True  Bool.False = Bool.False := rfl

-- Bool Laws
example (b : Bool.{0}) :
  Bool.not (Bool.not b) = b := rfl

example (a : Bool.{0}) (b : Bool.{0}) :
  Bool.not (Bool.and a b) =
    Bool.or (Bool.not a) (Bool.not b) := rfl

example (a : Bool.{0}) (b : Bool.{0}) :
  Bool.not (Bool.or a b) =
    Bool.and (Bool.not a) (Bool.not b) := rfl

example (a : Bool.{0}) (b : Bool.{0}) :
  Bool.implies a b = Bool.or (Bool.not a) b := rfl

-- Identity + Absorbing Laws
example (b : Bool.{0}) : Bool.and Bool.True b = b := rfl
example (b : Bool.{0}) : Bool.and b Bool.True = b := rfl
example (b : Bool.{0}) : Bool.and Bool.False b = Bool.False := rfl

example (b : Bool.{0}) : Bool.or Bool.False b = b := rfl
example (b : Bool.{0}) : Bool.or b Bool.False = b := rfl
example (b : Bool.{0}) : Bool.or Bool.True b = Bool.True := rfl

example (b : Bool.{0}) : Bool.xor Bool.False b = b := rfl
example (b : Bool.{0}) : Bool.xor b Bool.False = b := rfl
example (b : Bool.{0}) : Bool.xor Bool.True b = Bool.not b := rfl
example (b : Bool.{0}) : Bool.xor b Bool.True = Bool.not b := rfl

-- Associativity
example (a : Bool.{0}) (b : Bool.{0}) (c : Bool.{0}) :
  Bool.and (Bool.and a b) c = Bool.and a (Bool.and b c) := rfl

example (a : Bool.{0}) (b : Bool.{0}) (c : Bool.{0}) :
  Bool.or (Bool.or a b) c = Bool.or a (Bool.or b c) := rfl


end BoolTest

end NonInductiveTypeTheory
