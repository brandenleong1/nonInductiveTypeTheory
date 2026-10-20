import Constructs.Nat

namespace NonInductiveTypeTheory


universe u

def Tree (A : Type u) : Type (u + 1) :=
  ∀ (C : Type u), (A → C) → (C → C → C) → C

namespace Tree

def leaf {A : Type u} (a : A) : Tree A :=
  λ _C leaf _branch => leaf a

def branch {A : Type u} (tree0 : Tree A) (tree1 : Tree A) : Tree A :=
  λ C leaf branch => branch (tree0 C leaf branch) (tree1 C leaf branch)

def fold {A C : Type u} (tree : Tree A) (process_leaf : A → C) (process_branch : C → C → C) : C :=
  tree C process_leaf process_branch

def map {A B : Type u} (f : A → B) (tree : Tree A) : Tree B :=
  λ C leaf branch => tree C (λ a => leaf (f a)) branch

def size_leaves {A : Type u} (tree : Tree A) : Nat :=
  λ C s z =>
    let State : Type u := C → C
    let step_leaf : A → State :=
      λ _a =>
        λ c => s c
    let step_branch : State → State → State :=
      λ branch0 branch1 =>
        λ c => branch1 (branch0 c)
    let final_state : State :=
      tree State step_leaf step_branch
    final_state z

def size_nodes {A : Type u} (tree : Tree A) : Nat :=
  λ C s z =>
    let State : Type u := C → C
    let step_leaf : A → State :=
      λ _a =>
        λ c => s c
    let step_branch : State → State → State :=
      λ branch0 branch1 =>
        λ c => s (branch1 (branch0 c))
    let final_state : State :=
      tree State step_leaf step_branch
    final_state z

def mirror {A : Type u} (tree : Tree A) : Tree A :=
  λ C leaf branch => tree C leaf (λ left right => branch right left)

end Tree


end NonInductiveTypeTheory
