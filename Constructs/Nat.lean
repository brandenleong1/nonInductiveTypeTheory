namespace NonInductiveTypeTheory


universe u

def Nat : Type (u + 1) :=
  ∀ (C : Type u), (C → C) → C → C

namespace Nat

def Zero : Nat := λ _C _s z => z

def succ (n : Nat) : Nat :=
  λ C s z => s (n C s z)

def pred (n : Nat) : Nat :=
  λ C s z =>
    let Pair : Type u := (C → C → C) → C
    let pair : C → C → Pair :=
      λ a b select => select a b
    let get0 : Pair → C :=
      λ pair => pair (λ a _ => a)
    let get1 : Pair → C :=
      λ pair => pair (λ _ b => b)
    let step : Pair → Pair :=
      λ state =>
        pair (s (get0 state)) (get0 state)
    let final_state : Pair :=
      n Pair step (pair z z)
    get1 final_state

def add (m : Nat) (n : Nat) : Nat :=
  λ C s z => m C s (n C s z)

def mult (m : Nat) (n : Nat) : Nat :=
  λ C s z => m C (n C s) z

end Nat


end NonInductiveTypeTheory
