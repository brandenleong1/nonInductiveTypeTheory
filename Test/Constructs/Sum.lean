import Constructs.Sum

namespace NonInductiveTypeTheory

namespace SumTest


-- Construction and Projection
example {A B C : Type} (a : A) (onA : A → C) (onB : B → C) :
    Sum.sum0 (B := B) a C onA onB = onA a := rfl

example {A B C : Type} (b : B) (onA : A → C) (onB : B → C) :
    Sum.sum1 (A := A) b C onA onB = onB b := rfl

-- Swapping
example {A B : Type} (a : A) :
    Sum.swap (Sum.sum0 (B := B) a) = Sum.sum1 a := rfl

example {A B : Type} (b : B) :
    Sum.swap (Sum.sum1 (A := A) b) = Sum.sum0 b := rfl

example {A B : Type} (s : Sum A B) :
    Sum.swap (Sum.swap s) = s := rfl

-- Mapping Both Components
example {A B D E : Type} (f : A → D) (g : B → E) (a : A) :
    Sum.bimap f g (Sum.sum0 (B := B) a) = Sum.sum0 (B := E) (f a) := rfl

example {A B D E : Type} (f : A → D) (g : B → E) (b : B) :
    Sum.bimap f g (Sum.sum1 (A := A) b) = Sum.sum1 (A := D) (g b) := rfl

example {A B : Type} (s : Sum A B) :
    Sum.bimap (λ a => a) (λ b => b) s = s := rfl

example
    {A B D E F G : Type}
    (f1 : A → D) (f2 : D → F)
    (g1 : B → E) (g2 : E → G)
    (s : Sum A B) :
    Sum.bimap f2 g2 (Sum.bimap f1 g1 s) =
      Sum.bimap (λ a => f2 (f1 a)) (λ b => g2 (g1 b)) s := rfl

example {A B D E : Type} (f : A → D) (g : B → E) (s : Sum A B) :
    Sum.swap (Sum.bimap f g s) =
      Sum.bimap g f (Sum.swap s) := rfl


end SumTest

end NonInductiveTypeTheory
