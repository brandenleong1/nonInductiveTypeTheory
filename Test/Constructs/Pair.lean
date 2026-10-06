import Constructs.Pair

namespace NonInductiveTypeTheory

namespace PairTest


-- Construction and Projection
example {A B : Type} (a : A) (b : B) :
    Pair.get0 (Pair.pair a b) = a := rfl

example {A B : Type} (a : A) (b : B) :
    Pair.get1 (Pair.pair a b) = b := rfl

-- Swapping
example {A B : Type} (a : A) (b : B) :
    Pair.swap (Pair.pair a b) = Pair.pair b a := rfl

example {A B : Type} (p : Pair A B) :
    Pair.swap (Pair.swap p) = p := rfl

example {A B : Type} (p : Pair A B) :
    Pair.get0 (Pair.swap p) = Pair.get1 p := rfl

example {A B : Type} (p : Pair A B) :
    Pair.get1 (Pair.swap p) = Pair.get0 p := rfl

-- Mapping Both Components
example {A B D E : Type} (f : A → D) (g : B → E) (a : A) (b : B) :
    Pair.bimap f g (Pair.pair a b) = Pair.pair (f a) (g b) := rfl

example {A B : Type} (p : Pair A B) :
    Pair.bimap (λ a => a) (λ b => b) p = p := rfl

example
    {A B D E F G : Type}
    (f1 : A → D) (f2 : D → F)
    (g1 : B → E) (g2 : E → G)
    (p : Pair A B) :
    Pair.bimap f2 g2 (Pair.bimap f1 g1 p) =
      Pair.bimap (λ a => f2 (f1 a)) (λ b => g2 (g1 b)) p := rfl

example {A B D E : Type} (f : A → D) (g : B → E) (p : Pair A B) :
    Pair.swap (Pair.bimap f g p) =
      Pair.bimap g f (Pair.swap p) := rfl


end PairTest

end NonInductiveTypeTheory
