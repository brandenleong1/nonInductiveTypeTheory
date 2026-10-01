namespace NonInductiveTypeTheory


universe u

def Bool : Type (u + 1) :=
  ∀ (C : Type u), C → C → C

namespace Bool

def True  : Bool := λ _C t _ => t
def False : Bool := λ _C _ f => f

def Not (b : Bool) : Bool :=
  λ C t f => b C f t

def And (b1 : Bool) (b2 : Bool) : Bool :=
  λ C t f => b1 C (b2 C t f) f

def Or (b1 : Bool) (b2 : Bool) : Bool :=
  λ C t f => b1 C t (b2 C t f)

def Xor (b1 : Bool) (b2 : Bool) : Bool :=
  λ C t f => b1 C (b2 C f t) (b2 C t f)

def Implies (b1 : Bool) (b2 : Bool) : Bool :=
  λ C t f => b1 C (b2 C t f) t

end Bool


end NonInductiveTypeTheory
