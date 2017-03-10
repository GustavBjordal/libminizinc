include "ls-annotation.mzn";

include "globals.mzn";

set of int: N = 1..10;
set of int: V = 1..20;
array[N] of var V: Ys;

function ann: all_diff(array[int] of var int: Xs) :: neighbourhood_definition =
neighbourhood_and(neighbourhood_or(

from(i,j in index_set(Xs) where i<j)(
neighbourhood_and(neighbourhood_and(assign_array(Xs,i,Xs[j]),assign_array(Xs,j,Xs[i])), ensure(Xs[1] < Xs[max(index_set(Xs))]))
),

from(i in index_set(Xs), v in dom_array(Xs))(
assign_array(Xs,i,v)
)
), initialize(Xs[1] < Xs[2]));

solve :: all_diff(Ys) satisfy;