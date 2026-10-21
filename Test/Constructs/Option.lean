import Constructs.Option

namespace NonInductiveTypeTheory

namespace OptionTest


-- Construction
example {A C : Type} (c : C) (onA : A → C) :
    Option.none C c onA = c := rfl

example {A C : Type} (a : A) (c : C) (onA : A → C) :
    Option.some a C c onA = onA a := rfl

-- Mapping
example {A B : Type} (f : A → B) :
    Option.map f Option.none = Option.none := rfl

example {A B : Type} (f : A → B) (a : A) :
    Option.map f (Option.some a) = Option.some (f a) := rfl

example {A : Type} (o : Option A) :
    Option.map (λ a => a) o = o := rfl

example {A B C : Type} (f : A → B) (g : B → C) (o : Option A) :
    Option.map g (Option.map f o) =
      Option.map (λ a => g (f a)) o := rfl

-- Binding
example {A B : Type} (f : A → Option B) :
    Option.bind f Option.none = Option.none := rfl

example {A B : Type} (f : A → Option B) (a : A) :
    Option.bind f (Option.some a) = f a := rfl

-- Presence Checking
example {A : Type} :
    Option.is_some (Option.none : Option A) = Bool.False := rfl

example {A : Type} (a : A) :
    Option.is_some (Option.some a) = Bool.True := rfl


end OptionTest

end NonInductiveTypeTheory
