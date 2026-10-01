namespace NonInductiveTypeTheory


universe u

def Nat : Type (u + 1) :=
  ∀ (C : Type u), (C → C) → C → C

namespace Nat

def Zero : Nat := λ _C _s z => z

def Succ (n : Nat) : Nat :=
  λ C s z => s (n C s z)

def Add (m : Nat) (n : Nat) : Nat :=
  λ C s z => m C s (n C s z)

def Mult (m : Nat) (n : Nat) : Nat :=
  λ C s z => m C (n C s) z

end Nat


end NonInductiveTypeTheory
