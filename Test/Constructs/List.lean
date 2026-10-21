import Constructs.List

namespace NonInductiveTypeTheory

namespace ListTest


private def One   : Nat.{0} := Nat.succ Nat.Zero
private def Two   : Nat.{0} := Nat.succ One
private def Three : Nat.{0} := Nat.succ Two

-- Construction and Folding
example {A C : Type} (combine : A → C → C) (empty : C) :
    List.nil C combine empty = empty := rfl

example {A C : Type} (a : A) (list : List A)
    (combine : A → C → C) (empty : C) :
    List.cons a list C combine empty =
      combine a (list C combine empty) := rfl

-- Mapping
example {A B : Type} (f : A → B) :
    List.map f List.nil = List.nil := rfl

example {A B : Type} (f : A → B) (a : A) (list : List A) :
    List.map f (List.cons a list) =
      List.cons (f a) (List.map f list) := rfl

example {A : Type} (list : List A) :
    List.map (λ a => a) list = list := rfl

-- Binding
example {A B : Type} (f : A → List B) :
    List.bind f List.nil = List.nil := rfl

example {A B : Type} (f : A → List B) (a : A) (list : List A) :
    List.bind f (List.cons a list) =
      List.append (f a) (List.bind f list) := rfl

example {A B : Type} (f : A → List B) (a : A) :
    List.bind f (List.cons a List.nil) = f a := rfl

example {A : Type} (list : List A) :
    List.bind (λ a => List.cons a List.nil) list = list := rfl

example {A B C : Type} (f : A → List B) (g : B → List C)
    (list : List A) :
    List.bind g (List.bind f list) =
      List.bind (λ a => List.bind g (f a)) list := rfl

-- Appending
example {A : Type} (list : List A) :
    List.append List.nil list = list := rfl

example {A : Type} (list : List A) :
    List.append list List.nil = list := rfl

example {A : Type} (a : A) (xs ys : List A) :
    List.append (List.cons a xs) ys =
      List.cons a (List.append xs ys) := rfl

example {A : Type} (a b c : List A) :
    List.append (List.append a b) c =
      List.append a (List.append b c) := rfl

-- Length
example {A : Type} :
    List.length (List.nil : List A) = Nat.Zero := rfl

example {A : Type} (a : A) (list : List A) :
    List.length (List.cons a list) =
      Nat.succ (List.length list) := rfl

-- Head and Last
example {A : Type} :
    List.head (List.nil : List A) = Option.none := rfl

example {A : Type} (a : A) (list : List A) :
    List.head (List.cons a list) = Option.some a := rfl

example {A : Type} :
    List.last (List.nil : List A) = Option.none := rfl

example {A : Type} (a : A) :
    List.last (List.cons a List.nil) = Option.some a := rfl

example {A : Type} (a b c : A) :
    List.last
        (List.cons a (List.cons b (List.cons c List.nil))) =
      Option.some c := rfl

-- Reverse
example {A : Type} :
    List.reverse (List.nil : List A) = List.nil := rfl

example {A : Type} (a : A) :
    List.reverse (List.cons a List.nil) =
      List.cons a List.nil := rfl

example {A : Type} (a b c : A) :
    List.reverse
        (List.cons a (List.cons b (List.cons c List.nil))) =
      List.cons c (List.cons b (List.cons a List.nil)) := rfl

-- Tail
example {A : Type} :
    List.tail (List.nil : List A) = List.nil := rfl

example {A : Type} (a : A) :
    List.tail (List.cons a List.nil) = List.nil := rfl

example {A : Type} (a b c : A) :
    List.tail
        (List.cons a (List.cons b (List.cons c List.nil))) =
      List.cons b (List.cons c List.nil) := rfl

-- Emptiness
example {A : Type} :
    List.is_empty (List.nil : List A) = Bool.True := rfl

example {A : Type} (a : A) (list : List A) :
    List.is_empty (List.cons a list) = Bool.False := rfl

-- Filtering
example {A : Type} (list : List A) :
    List.filter (λ _ => Bool.True) list = list := rfl

example {A : Type} (a b : A) :
    List.filter (λ _ => Bool.False)
        (List.cons a (List.cons b List.nil)) =
      List.nil := rfl

-- Quantifiers
example {A : Type} (cond : A → Bool) :
    List.any cond List.nil = Bool.False := rfl

example {A : Type} (cond : A → Bool) (a : A) (list : List A) :
    List.any cond (List.cons a list) =
      Bool.or (cond a) (List.any cond list) := rfl

example {A : Type} (cond : A → Bool) :
    List.all cond List.nil = Bool.True := rfl

example {A : Type} (cond : A → Bool) (a : A) (list : List A) :
    List.all cond (List.cons a list) =
      Bool.and (cond a) (List.all cond list) := rfl

-- Searching
example {A : Type} (cond : A → Bool) :
    List.find cond List.nil = Option.none := rfl

example {A : Type} (a b : A) :
    List.find (λ _ => Bool.False)
        (List.cons a (List.cons b List.nil)) =
      Option.none := rfl

example {A : Type} (a : A) :
    List.find (λ _ => Bool.True) (List.cons a List.nil) =
      Option.some a := rfl

example {A : Type} (a b c : A) :
    List.find (λ _ => Bool.True)
        (List.cons a (List.cons b (List.cons c List.nil))) =
      Option.some a := rfl

example {A : Type} (a b : A) :
    List.find_last (λ _ => Bool.False)
        (List.cons a (List.cons b List.nil)) =
      Option.none := rfl

example {A : Type} (a : A) :
    List.find_last (λ _ => Bool.True) (List.cons a List.nil) =
      Option.some a := rfl

example {A : Type} (a b c : A) :
    List.find_last (λ _ => Bool.True)
        (List.cons a (List.cons b (List.cons c List.nil))) =
      Option.some c := rfl

-- Counting
example {A : Type} :
    List.count (λ _ => Bool.True) (List.nil : List A) =
      Nat.Zero := rfl

example {A : Type} (a : A) :
    List.count (λ _ => Bool.True) (List.cons a List.nil) =
      One := rfl

example {A : Type} (a b c : A) :
    List.count (λ _ => Bool.False)
        (List.cons a (List.cons b (List.cons c List.nil))) =
      Nat.Zero := rfl

example {A : Type} (a b c : A) :
    List.count (λ _ => Bool.True)
        (List.cons a (List.cons b (List.cons c List.nil))) =
      Three := rfl

example {A : Type} (list : List A) :
    List.count (λ _ => Bool.True) list =
      List.length list := rfl


end ListTest

end NonInductiveTypeTheory
