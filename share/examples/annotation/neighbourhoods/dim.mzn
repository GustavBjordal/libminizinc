include "ls-annotation.mzn";

include "globals.mzn";
int: n = 5;
set of int: N = 1..n;
set of int: V = 0..n*n;
array[1..3,N,1..2] of var V: Xs;
array[1..3,N,] of var V: Ys;

constraint  Xs[1,1,1] = 0;
constraint  Xs[1,1,2] = 1;
constraint  Xs[1,2,1] = 3;
constraint  Xs[1,2,2] = 4;
constraint  Xs[2,2,2] = 11;

constraint Ys[1,1] = 1;
constraint Ys[1,2] = 2;
constraint Ys[1,3] = 3;
constraint Ys[2,1] = 1;
constraint Ys[2,2] = 2;

function ann: dim() :: neighbourhood_definition =
initialize(
alldifferent(array1d(Xs))
/\ Xs[1,2,2] = 4
)
/\
from(i in 1..3, j in N, k in 2..3)
      (Xs[1,2,2] :=: Xs[i,j,k])
;

solve :: neighbourhood_and([dim()]) satisfy; %minimize Ys[1,1]+Ys[1,3]+Ys[3,3]+Ys[3,1];
