neighbourhood <- 
    from((variable in dom)+ (where constraint (/\ constraint)*)? )(
    move (/\ move)*
    (/\ ensure (constraint)*)?
    ) /\ initialize((constraint)*);

move <- 
    (variable | array access) := (variable | value)
  | (variable | array access) := (variable | value | array access)
  %until we have the new opertators ->
    swap_array(array,(variable | value),array,(variable | value))
  | assign_array(array,(variable | value),(variable | value))
  | swap(variable,(variable | value),variable,(variable | value))
  | assign(variable,(variable | value),(variable | value))