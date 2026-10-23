import Logic.Basic

namespace NonInductiveTypeTheory
namespace Logic


def And (P : Prop) (Q : Prop) : Prop :=
  ∀ (C : Prop), (P → Q → C) → C

namespace And

theorem and {P Q : Prop} (p : P) (q : Q) : And P Q :=
  λ _C and => and p q

theorem left {P Q : Prop} (h : And P Q) : P :=
  h P (λ p _q => p)

theorem right {P Q : Prop} (h : And P Q) : Q :=
  h Q (λ _p q => q)

theorem map {P Q R S : Prop} (f : P → R) (g : Q → S) (h : And P Q) : And R S :=
  λ _C and => and (f (left h)) (g (right h))

theorem commutative {P Q : Prop} (h : And P Q) : And Q P :=
  λ _C and => and (right h) (left h)

theorem associative.forward {P Q R : Prop} (h : And (And P Q) R) : And P (And Q R) :=
  λ _C and0 => and0 (left (left h)) (λ _C and1 => and1 (right (left h)) (right h))

theorem associative.backward {P Q R : Prop} (h : And P (And Q R)) : And (And P Q) R :=
  λ _C and0 => and0 (λ _C and1 => and1 (left h) (left (right h))) (right (right h))

theorem idempotent.expand {P : Prop} (p : P) : And P P :=
  λ _C and => and p p

theorem idempotent.eliminate {P : Prop} (h : And P P) : P :=
  h P (λ p0 _p1 => p0)

theorem curry {P Q R : Prop} (f : And P Q → R) : P → Q → R :=
  λ p q => f (λ _C and => and p q)

theorem uncurry {P Q R : Prop} (f : P → Q → R) : And P Q → R :=
  λ h => h R f

theorem identity.top.expand {P : Prop} (p : P) : And P Top :=
  λ _C and => and p (λ _C p => p)

theorem identity.top.eliminate {P : Prop} (h : And P Top) : P :=
  left h

theorem identity.bottom.expand {P : Prop} (bottom : Bottom) : And P Bottom :=
  λ C _and => bottom C

theorem identity.bottom.eliminate {P : Prop} (h : And P Bottom) : Bottom :=
  λ C => h C (λ _p bottom => bottom C)

end And


end Logic
end NonInductiveTypeTheory
