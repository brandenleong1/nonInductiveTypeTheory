namespace NonInductiveTypeTheory


universe u

def Pair (A : Type u) (B : Type u) : Type (u + 1) :=
  ∀ (C : Type u), (A → B → C) → C

namespace Pair

def pair {A B : Type u} (a : A) (b : B) : Pair A B :=
  λ _C wrap => wrap a b

def get0 {A B : Type u} (p : Pair A B) : A :=
  p A (λ a _ => a)

def get1 {A B : Type u} (p : Pair A B) : B :=
  p B (λ _ b => b)

def swap {A B : Type u} (p : Pair A B) : Pair B A :=
  λ C wrap =>
    p C (λ a b => wrap b a)

def bimap {A B D E : Type u} (f : A → D) (g : B → E) (p : Pair A B) : Pair D E :=
  λ C wrap => p C (λ a b => wrap (f a) (g b))

end Pair


end NonInductiveTypeTheory
