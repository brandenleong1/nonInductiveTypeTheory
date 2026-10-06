import Constructs.Box

namespace NonInductiveTypeTheory

namespace BoxTest


-- Computation
example {A : Type} (a : A) : Box.get0 (Box.box a) = a := rfl

example {A B : Type} (f : A → B) (a : A) :
    Box.map f (Box.box a) = Box.box (f a) := rfl

-- Box Laws
example {A : Type} (b : Box A) :
    Box.map (λ a => a) b = b := rfl

example {A B C : Type} (f : A → B) (g : B → C) (b : Box A) :
    Box.map g (Box.map f b) = Box.map (λ a => g (f a)) b := rfl


end BoxTest

end NonInductiveTypeTheory
