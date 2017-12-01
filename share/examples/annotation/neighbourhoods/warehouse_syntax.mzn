include "ls-annotation.mzn";

include "globals.mzn";
int: w = 10;
int: s = 10;
int: is_open_cost = 100;
set of int: O = {2,4};
% array[1..w,1..s] of int: transportation_cost =
% [|1,2,3,4,5,6,7,8,9,10
% |1,2,3,4,5,6,7,8,9,10
% |1,2,3,4,5,6,7,8,9,10
% |1,2,3,4,5,6,7,8,9,10
% |1,2,3,4,5,6,7,8,9,10|];
% Some decision variables omitted

predicate foobar(array[int] of var int: foo);

array[1..w] of var 0..2: open;

constraint sum(open) <= 3;

% function ann: warehouse_switch(array [int] of var int: status) :: neighbourhood_definition =
%     from(i in index_set(status))(
%        status[i] := 1-(status[i]) /\
%        ensure(exists(o in O)(status[o] = 1) /\ status[i] = 1)
%      )
% ;
% function ann: warehouse_swap(array [int] of var int: status) :: neighbourhood_definition =
% from(i, j in index_set(status) where i<j /\ status[i] != status[j])(
%         status[i] := status[j] /\
%         status[j] := status[i] /\
%         ensure(exists(o in O)(status[o] = 1)))
%         /\ initialize(status[1] = 1);

        
function ann: warehouse_both(array [int] of var int: status) :: neighbourhood_definition =
from(i, j in index_set(status) where i<j /\ status[i] != status[j])(
        status[i] :=: status[j] /\
        ensure(exists(o in O)(status[o] = 1)))
\/
from(i in index_set(status))(
       status[i] := 1-(status[i]) /\
       ensure(exists(o in O)(status[o] = 1)))
/\ initialize(forall(i in index_set(status))(status[i] = (i-1) mod 3));

solve :: neighbourhood_and([warehouse_both(open)]) satisfy;