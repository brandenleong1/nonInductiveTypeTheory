namespace NonInductiveTypeTheory


universe u

def Unit : Type (u + 1) :=
  ∀ (C : Type u), C → C

namespace Unit

def unit : Unit :=
  λ _C c => c

end Unit


end NonInductiveTypeTheory
