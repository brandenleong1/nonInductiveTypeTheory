import Logic.And
import Logic.Basic

namespace NonInductiveTypeTheory
namespace Logic


def Or (P : Prop) (Q : Prop) : Prop :=
  ∀ (C : Prop), (P → C) → (Q → C) → C

namespace Or

theorem left {P Q : Prop} (p : P) : Or P Q :=
  λ _C orP _orQ => orP p

theorem right {P Q : Prop} (q : Q) : Or P Q :=
  λ _C _orP orQ => orQ q

theorem map {P Q R S : Prop} (f : P → R) (g : Q → S) (h : Or P Q) : Or R S :=
  λ C orR orS => h C (λ p => orR (f p)) (λ q => orS (g q))

theorem commutative {P Q : Prop} (h : Or P Q) : Or Q P :=
  λ C orQ orP => h C (λ p => orP p) (λ q => orQ q)

theorem associative.forward {P Q R : Prop} (h : Or (Or P Q) R) : Or P (Or Q R) :=
  h (Or P (Or Q R))
    (λ pq => 
      pq (Or P (Or Q R)) (λ p => left p) (λ q => right (left q)))
    (λ r => right (right r))

theorem associative.backward {P Q R : Prop} (h : Or P (Or Q R)) : Or (Or P Q) R :=
  h (Or (Or P Q) R)
    (λ p => left (left p))
    (λ qr =>
      qr (Or (Or P Q) R) (λ q => left (right q)) (λ r => right r))

theorem idempotent.expand {P : Prop} (p : P) : Or P P :=
  λ _C orP0 _orP1 => orP0 p

theorem idempotent.eliminate {P : Prop} (h : Or P P) : P :=
  h P (λ p => p) (λ p => p)

theorem curry {P Q R : Prop} (f : Or P Q → R) : And (P → R) (Q → R) :=
  And.and (λ p => f (Or.left p)) (λ q => f (Or.right q))

theorem uncurry {P Q R : Prop} (f : And (P → R) (Q → R)) : Or P Q → R :=
  λ h => h R (And.left f) (And.right f)

theorem identity.top.expand {P : Prop} (top : Top) : Or P Top :=
  right top

theorem identity.top.eliminate {P : Prop} (_h : Or P Top) : Top :=
  λ _C c => c

theorem identity.bottom.expand {P : Prop} (p : P) : Or P Bottom :=
  left p

theorem identity.bottom.eliminate {P : Prop} (h : Or P Bottom) : P :=
  h P (λ c => c) (λ bottom => bottom P)

end Or


end Logic
end NonInductiveTypeTheory
