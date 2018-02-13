include "ls-annotation.mzn";

include "globals.mzn";
int: n = 10;
set of int: N = 1..n;
set of int: V = 1..n*n;
array[N,N] of var V: Ys;

int: magic_number = sum(V) div n ;

constraint forall(i in N)(sum(j in N)(Ys[i,j]) = magic_number);
constraint forall(i in N)(sum(j in N)(Ys[j,i]) = magic_number);

constraint sum(i in N)(Ys[i,i]) = magic_number;
constraint sum(i in N)(Ys[i,n-i+1]) = magic_number;

function ann: all_diff(array [int] of var int: Xs) :: neighbourhood_definition =
initialize(
alldifferent(Xs)
)
/\
from(i, j in index_set(Xs) where i<j)
      (Xs[i] :=: Xs[j])
 \/
 from(i in index_set(Xs), v in dom_array(Xs) 
         where forall(j in index_set(Xs))(Xs[j] != v)
         )(Xs[i] := v);

solve :: neighbourhood_and([all_diff(array1d(Ys))]) satisfy; %minimize Ys[1,1]+Ys[1,3]+Ys[3,3]+Ys[3,1];
