import Constructs.Bool
import Constructs.Nat
import Constructs.Option

namespace NonInductiveTypeTheory


universe u

def List (A : Type u) : Type (u + 1) :=
  ∀ (C : Type u), (A → C → C) → C → C

namespace List

def nil {A : Type u} : List A :=
  λ _C _combine empty => empty

def cons {A : Type u} (a : A) (list : List A) : List A :=
  λ C combine empty => combine a (list C combine empty)

def map {A B : Type u} (f : A → B) (list : List A) : List B :=
  λ C combine empty => list C (λ a => combine (f a)) empty

def bind {A B : Type u} (f : A → List B) (list : List A) : List B :=
  λ C combine empty => list C (λ a => (f a) C combine) empty

def append {A : Type u} (list_from : List A) (list_to : List A) : List A :=
  λ C combine empty => list_from C combine (list_to C combine empty)

def length {A : Type u} (list : List A) : Nat :=
  λ C s z => list C (λ _ c => s c) z

def head {A : Type u} (list : List A) : Option A :=
  λ C c onA => list C (λ a _ => onA a) c

def last {A : Type u} (list : List A) : Option A :=
  λ C c onA =>
    let State : Type u := C → (A → C) → C
    let none_state : State :=
      λ none _some => none
    let step : A → State → State :=
      λ a state =>
        λ _none some => state (some a) some
    let final_state : State :=
      list State step none_state
    final_state c onA

def reverse {A : Type u} (list : List A) : List A :=
  λ C combine empty =>
    let State : Type u := C → C
    let id : State :=
      λ c => c
    let step : A → State → State :=
      λ a state =>
        λ c => state (combine a c)
    let final_state : State :=
      list State step id
    final_state empty

def tail {A : Type u} (list : List A) : List A :=
  λ C combine empty =>
    let Pair : Type u := (C → C → C) → C
    let pair : C → C → Pair :=
      λ a b select => select a b
    let get0 : Pair → C :=
      λ pair => pair (λ a _ => a)
    let get1 : Pair → C :=
      λ pair => pair (λ _ b => b)
    let step : A → Pair → Pair :=
      λ a state =>
        pair (combine a (get0 state)) (get0 state)
    let final_state : Pair :=
      list Pair step (pair empty empty)
    get1 final_state

def is_empty {A : Type u} (list : List A) : Bool :=
  λ C t f => list C (λ _ _ => f) t

def filter {A : Type u} (f : A → Bool) (list : List A) : List A :=
  λ C combine empty => list C (λ a c => ((f a) C (combine a c) (c))) empty

def any {A : Type u} (cond : A → Bool) (list : List A) : Bool :=
  λ C t f => list C (λ a c => (cond a) C t c) f

def all {A : Type u} (cond : A → Bool) (list : List A) : Bool :=
  λ C t f => list C (λ a c => (cond a) C c f) t

def find {A : Type u} (cond : A → Bool) (list : List A) : Option A :=
  λ C c onA => list C (λ a c => (cond a) C (onA a) c) c

def find_last {A : Type u} (cond : A → Bool) (list : List A) : Option A :=
  find cond (reverse list)

def count {A : Type u} (cond : A → Bool) (list : List A) : Nat :=
  λ C s z => list C (λ a c => (cond a) C (s c) c) z

end List


end NonInductiveTypeTheory
