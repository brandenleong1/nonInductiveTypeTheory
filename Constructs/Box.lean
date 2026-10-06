namespace NonInductiveTypeTheory


universe u

def Box (A : Type u) : Type (u + 1) :=
  ∀ (C : Type u), (A → C) → C

namespace Box

def box {A : Type u} (a : A) : Box A :=
  λ _C wrap => wrap a

def get0 {A : Type u} (b : Box A) : A :=
  b A (λ a => a)

def map {A B : Type u} (f : A → B) (b : Box A) : Box B :=
  λ C wrap => b C (λ a => wrap (f a))

end Box


end NonInductiveTypeTheory
