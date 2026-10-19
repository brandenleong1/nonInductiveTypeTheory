namespace NonInductiveTypeTheory


universe u

-- Equivalent to std::optional<A>
def Option (A : Type u) : Type (u + 1) :=
  ∀ (C : Type u), C → (A → C) → C

namespace Option

def none {A : Type u} : Option A :=
  λ _C c _onA => c

def some {A : Type u} (a : A) : Option A :=
  λ _C _c onA => onA a

def map {A B : Type u} (f : A → B) (o : Option A) : Option B :=
  λ C c onB =>
    o C c (λ a => onB (f a))

def bind {A B : Type u} (f : A → Option B) (o : Option A) : Option B :=
  λ C c onB =>
    o C c (λ a => (f a) C c onB)

end Option


end NonInductiveTypeTheory
