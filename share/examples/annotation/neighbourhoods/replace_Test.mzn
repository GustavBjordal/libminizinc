include "ls-annotation.mzn";
include "globals.mzn";
set of int: N = 1..10;
set of int: V = 1..20;
array [N] of var V: Ys;
var int: foo;
function ann: all_diff(array [int] of var int: Xs, var dom_array(Xs): y) =
  let{constraint Xs[y] < y;}in domain;

solve :: all_diff(Ys,foo) satisfy;