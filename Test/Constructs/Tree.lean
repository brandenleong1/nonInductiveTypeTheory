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

-- Binding
example {A B : Type} (f : A → Tree B) (a : A) :
    Tree.bind f (Tree.leaf a) = f a := rfl

example {A B : Type} (f : A → Tree B) (left right : Tree A) :
    Tree.bind f (Tree.branch left right) =
      Tree.branch (Tree.bind f left) (Tree.bind f right) := rfl

example {A : Type} (tree : Tree A) :
    Tree.bind Tree.leaf tree = tree := rfl

example {A B C : Type} (f : A → Tree B) (g : B → Tree C)
    (tree : Tree A) :
    Tree.bind g (Tree.bind f tree) =
      Tree.bind (λ a => Tree.bind g (f a)) tree := rfl

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

-- Quantifiers
example {A : Type} (cond : A → Bool) (a : A) :
    Tree.any cond (Tree.leaf a) = cond a := rfl

example {A : Type} (cond : A → Bool) (left right : Tree A) :
    Tree.any cond (Tree.branch left right) =
      Bool.or (Tree.any cond left) (Tree.any cond right) := rfl

example {A : Type} (cond : A → Bool) (a : A) :
    Tree.all cond (Tree.leaf a) = cond a := rfl

example {A : Type} (cond : A → Bool) (left right : Tree A) :
    Tree.all cond (Tree.branch left right) =
      Bool.and (Tree.all cond left) (Tree.all cond right) := rfl

-- Searching
example {A : Type} (a : A) :
    Tree.find (λ _ => Bool.False) (Tree.leaf a) =
      Option.none := rfl

example {A : Type} (a : A) :
    Tree.find (λ _ => Bool.True) (Tree.leaf a) =
      Option.some a := rfl

example {A : Type} (a b c : A) :
    Tree.find (λ _ => Bool.False)
        (Tree.branch (Tree.leaf a)
          (Tree.branch (Tree.leaf b) (Tree.leaf c))) =
      Option.none := rfl

example {A : Type} (a b c : A) :
    Tree.find (λ _ => Bool.True)
        (Tree.branch (Tree.leaf a)
          (Tree.branch (Tree.leaf b) (Tree.leaf c))) =
      Option.some a := rfl

-- Counting
example {A : Type} (a : A) :
    Tree.count (λ _ => Bool.True) (Tree.leaf a) =
      One := rfl

example {A : Type} (a b c : A) :
    Tree.count (λ _ => Bool.False)
        (Tree.branch (Tree.leaf a)
          (Tree.branch (Tree.leaf b) (Tree.leaf c))) =
      Nat.Zero := rfl

example {A : Type} (a b c : A) :
    Tree.count (λ _ => Bool.True)
        (Tree.branch (Tree.leaf a)
          (Tree.branch (Tree.leaf b) (Tree.leaf c))) =
      Three := rfl

example {A : Type} (a b c : A) :
    Tree.count (λ _ => Bool.True)
        (Tree.branch (Tree.leaf a)
          (Tree.branch (Tree.leaf b) (Tree.leaf c))) =
      Tree.size_leaves
        (Tree.branch (Tree.leaf a)
          (Tree.branch (Tree.leaf b) (Tree.leaf c))) := rfl

-- Extremal Leaves
example {A : Type} (a : A) :
    Tree.leftmost (Tree.leaf a) = a := rfl

example {A : Type} (a : A) :
    Tree.rightmost (Tree.leaf a) = a := rfl

example {A : Type} (a b c : A) :
    Tree.leftmost
        (Tree.branch (Tree.leaf a)
          (Tree.branch (Tree.leaf b) (Tree.leaf c))) =
      a := rfl

example {A : Type} (a b c : A) :
    Tree.rightmost
        (Tree.branch (Tree.leaf a)
          (Tree.branch (Tree.leaf b) (Tree.leaf c))) =
      c := rfl

example {A : Type} (tree : Tree A) :
    Tree.leftmost (Tree.mirror tree) =
      Tree.rightmost tree := rfl

example {A : Type} (tree : Tree A) :
    Tree.rightmost (Tree.mirror tree) =
      Tree.leftmost tree := rfl

-- Conversion to List
example {A : Type} (a : A) :
    Tree.to_list (Tree.leaf a) =
      List.cons a List.nil := rfl

example {A : Type} (a b c : A) :
    Tree.to_list
        (Tree.branch (Tree.leaf a)
          (Tree.branch (Tree.leaf b) (Tree.leaf c))) =
      List.cons a (List.cons b (List.cons c List.nil)) := rfl

example {A : Type} (a b c : A) :
    List.length
        (Tree.to_list
          (Tree.branch (Tree.leaf a)
            (Tree.branch (Tree.leaf b) (Tree.leaf c)))) =
      Tree.size_leaves
        (Tree.branch (Tree.leaf a)
          (Tree.branch (Tree.leaf b) (Tree.leaf c))) := rfl

example {A : Type} (a b c : A) :
    Tree.to_list
        (Tree.mirror
          (Tree.branch (Tree.leaf a)
            (Tree.branch (Tree.leaf b) (Tree.leaf c)))) =
      List.reverse
        (Tree.to_list
          (Tree.branch (Tree.leaf a)
            (Tree.branch (Tree.leaf b) (Tree.leaf c)))) := rfl


end TreeTest

end NonInductiveTypeTheory
