macro "rfl_test " name:ident " : " stmt:term : command =>
  `(theorem $name : $stmt := rfl
    #print axioms $name)
