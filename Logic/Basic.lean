namespace NonInductiveTypeTheory
namespace Logic


def Top : Prop :=
  ∀ (C : Prop), C → C

def Bottom : Prop :=
  ∀ (C : Prop), C

theorem truth : Top :=
  λ _C c => c

theorem explode {P : Prop} (false : Bottom) : P :=
  false P

def not (P : Prop) : Prop :=
  P → Bottom


end Logic
end NonInductiveTypeTheory
