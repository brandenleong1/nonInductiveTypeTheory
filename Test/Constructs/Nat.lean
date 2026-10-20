import Constructs.Nat

namespace NonInductiveTypeTheory

namespace NatTest


private def One   : Nat.{0} := Nat.Succ Nat.Zero
private def Two   : Nat.{0} := Nat.Succ One
private def Three : Nat.{0} := Nat.Succ Two
private def Four  : Nat.{0} := Nat.Succ Three
private def Five  : Nat.{0} := Nat.Succ Four
private def Six   : Nat.{0} := Nat.Succ Five

-- Computation on Nat
example : Nat.Pred Nat.Zero = Nat.Zero := rfl
example : Nat.Pred One = Nat.Zero := rfl
example : Nat.Pred Two = One := rfl
example : Nat.Pred Three = Two := rfl
example : Nat.Pred Six = Five := rfl

example : Nat.Add  Two   Three = Five := rfl
example : Nat.Add  Three Two   = Five := rfl
example : Nat.Mult Two   Three = Six  := rfl
example : Nat.Mult Three Two   = Six  := rfl

-- Nat Laws
example (n : Nat.{0}) : Nat.Add Nat.Zero n = n := rfl
example (n : Nat.{0}) : Nat.Add n Nat.Zero = n := rfl

example (m : Nat.{0}) (n : Nat.{0}) :
    Nat.Add (Nat.Succ m) n = Nat.Succ (Nat.Add m n) := rfl

example (m : Nat.{0}) (n : Nat.{0}) (p : Nat.{0}) :
    Nat.Add (Nat.Add m n) p = Nat.Add m (Nat.Add n p) := rfl

example (n : Nat.{0}) : Nat.Mult Nat.Zero n = Nat.Zero := rfl

example (m : Nat.{0}) (n : Nat.{0}) :
    Nat.Mult (Nat.Succ m) n = Nat.Add n (Nat.Mult m n) := rfl


end NatTest

end NonInductiveTypeTheory
