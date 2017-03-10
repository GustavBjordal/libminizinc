annotation new_constraint_context;

var int:x;
var int:y;

constraint x<y;

constraint (let{
    var int: foo;
  }in 
  (let{ var int: bar;} in x<y /\ bar < y) 
  /\ x<y /\ foo <x) :: new_constraint_context :: domain;

constraint x<y;

solve satisfy;