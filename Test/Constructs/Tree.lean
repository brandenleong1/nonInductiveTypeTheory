import Constructs.Tree

namespace NonInductiveTypeTheory

namespace TreeTest


private def One   : Nat.{0} := Nat.succ Nat.Zero
private def Two   : Nat.{0} := Nat.succ One
private def Three : Nat.{0} := Nat.succ Two
private def Four  : Nat.{0} := Nat.succ Three
private def Five  : Nat.{0} := Nat.succ Four

-- Construction and Folding
example {A C : Type} (a : A) (process_leaf : A → C)
    (process_branch : C → C → C) :
    Tree.fold (Tree.leaf a) process_leaf process_branch =
      process_leaf a := rfl

example {A C : Type} (left right : Tree A) (process_leaf : A → C)
    (process_branch : C → C → C) :
    Tree.fold (Tree.branch left right) process_leaf process_branch =
      process_branch
        (Tree.fold left process_leaf process_branch)
        (Tree.fold right process_leaf process_branch) := rfl

-- Mapping
example {A B : Type} (f : A → B) (a : A) :
    Tree.map f (Tree.leaf a) = Tree.leaf (f a) := rfl

example {A B : Type} (f : A → B) (left right : Tree A) :
    Tree.map f (Tree.branch left right) =
      Tree.branch (Tree.map f left) (Tree.map f right) := rfl

example {A : Type} (tree : Tree A) :
    Tree.map (λ a => a) tree = tree := rfl

example {A B C : Type} (f : A → B) (g : B → C) (tree : Tree A) :
    Tree.map g (Tree.map f tree) =
      Tree.map (λ a => g (f a)) tree := rfl

-- Size
example {A : Type} (a : A) :
    Tree.size_leaves (Tree.leaf a) = One := rfl

example {A : Type} (a : A) :
    Tree.size_nodes (Tree.leaf a) = One := rfl

example {A : Type} (a b c : A) :
    Tree.size_leaves
        (Tree.branch (Tree.leaf a)
          (Tree.branch (Tree.leaf b) (Tree.leaf c))) =
      Three := rfl

example {A : Type} (a b c : A) :
    Tree.size_nodes
        (Tree.branch (Tree.leaf a)
          (Tree.branch (Tree.leaf b) (Tree.leaf c))) =
      Five := rfl

-- Mirroring
example {A : Type} (a : A) :
    Tree.mirror (Tree.leaf a) = Tree.leaf a := rfl

example {A : Type} (left right : Tree A) :
    Tree.mirror (Tree.branch left right) =
      Tree.branch (Tree.mirror right) (Tree.mirror left) := rfl

example {A : Type} (tree : Tree A) :
    Tree.mirror (Tree.mirror tree) = tree := rfl

example {A B : Type} (f : A → B) (tree : Tree A) :
    Tree.mirror (Tree.map f tree) =
      Tree.map f (Tree.mirror tree) := rfl


end TreeTest

end NonInductiveTypeTheory
