import Constructs.Nat

namespace NonInductiveTypeTheory

namespace NatTest


private def One   : Nat.{0} := Nat.succ Nat.Zero
private def Two   : Nat.{0} := Nat.succ One
private def Three : Nat.{0} := Nat.succ Two
private def Four  : Nat.{0} := Nat.succ Three
private def Five  : Nat.{0} := Nat.succ Four
private def Six   : Nat.{0} := Nat.succ Five

-- Computation on Nat
example : Nat.pred Nat.Zero = Nat.Zero := rfl
example : Nat.pred One = Nat.Zero := rfl
example : Nat.pred Two = One := rfl
example : Nat.pred Three = Two := rfl
example : Nat.pred Six = Five := rfl

example : Nat.add  Two   Three = Five := rfl
example : Nat.add  Three Two   = Five := rfl
example : Nat.mult Two   Three = Six  := rfl
example : Nat.mult Three Two   = Six  := rfl

-- Zero Checking
example : Nat.is_zero Nat.Zero = Bool.True := rfl

example (n : Nat.{0}) :
    Nat.is_zero (Nat.succ n) = Bool.False := rfl

-- Nat Laws
example (n : Nat.{0}) : Nat.add Nat.Zero n = n := rfl
example (n : Nat.{0}) : Nat.add n Nat.Zero = n := rfl

example (m : Nat.{0}) (n : Nat.{0}) :
    Nat.add (Nat.succ m) n = Nat.succ (Nat.add m n) := rfl

example (m : Nat.{0}) (n : Nat.{0}) (p : Nat.{0}) :
    Nat.add (Nat.add m n) p = Nat.add m (Nat.add n p) := rfl

example (n : Nat.{0}) : Nat.mult Nat.Zero n = Nat.Zero := rfl

example (m : Nat.{0}) (n : Nat.{0}) :
    Nat.mult (Nat.succ m) n = Nat.add n (Nat.mult m n) := rfl


end NatTest

end NonInductiveTypeTheory
