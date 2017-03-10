include "neighbourhood/ls-annotation.mzn";
var int: x;
var int: y;
annotation bob;
annotation bar(ann: b);

function ann: ensure(ann: move, var bool: cons, var bool ctx) =
(let
{constraint cons :: ls_post_condition(ctx)}
in
move
)::new_constraint_context;


solve::bar(foo(x<y)) satisfy;

neighbourhood <- 
  from((variable in dom)+ where (constraint)*)(
  move (/\ move)*
  (ensure (constraint)*)?
  ) :: initialize((constraint)*);

move <- (variable | array access) := value
  | (variable | array access) := (variable | array access)