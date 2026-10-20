import Constructs.List

namespace NonInductiveTypeTheory

namespace ListTest


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
      Nat.Succ (List.length list) := rfl

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


end ListTest

end NonInductiveTypeTheory
