namespace NonInductiveTypeTheory


universe u

def Bool : Type (u + 1) :=
  ∀ (C : Type u), C → C → C

namespace Bool

def True  : Bool := λ _C t _ => t
def False : Bool := λ _C _ f => f

def not (b : Bool) : Bool :=
  λ C t f => b C f t

def and (b1 : Bool) (b2 : Bool) : Bool :=
  λ C t f => b1 C (b2 C t f) f

def or (b1 : Bool) (b2 : Bool) : Bool :=
  λ C t f => b1 C t (b2 C t f)

def xor (b1 : Bool) (b2 : Bool) : Bool :=
  λ C t f => b1 C (b2 C f t) (b2 C t f)

def implies (b1 : Bool) (b2 : Bool) : Bool :=
  λ C t f => b1 C (b2 C t f) t

end Bool


end NonInductiveTypeTheory
