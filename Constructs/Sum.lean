namespace NonInductiveTypeTheory


universe u

-- Equivalent to std::variant<A, B>
def Sum (A : Type u) (B : Type u) : Type (u + 1) :=
  ∀ (C : Type u), (A → C) → (B → C) → C

namespace Sum

def sum0 {A B : Type u} (a : A) : Sum A B :=
  λ _C onA _onB => onA a

def sum1 {A B : Type u} (b : B) : Sum A B :=
  λ _C _onA onB => onB b

def swap {A B : Type u} (s : Sum A B) : Sum B A :=
  λ C onB onA =>
    s C (λ a => onA a) (λ b => onB b)

def bimap {A B D E : Type u} (f : A → D) (g : B → E) (s : Sum A B) : Sum D E :=
  λ C onD onE =>
    s C (λ a => onD (f a)) (λ b => onE (g b))

end Sum


end NonInductiveTypeTheory
