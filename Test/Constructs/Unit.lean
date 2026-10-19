import Constructs.Unit

namespace NonInductiveTypeTheory


-- Construction
example {C : Type} (c : C) :
    Unit.unit C c = c := rfl

-- Composition
example {C D : Type} (f : C → D) (c : C) :
    Unit.unit D (f (Unit.unit C c)) = f c := rfl


end NonInductiveTypeTheory
