include "globals.mzn";

set of int: N = 1..10;
array[N] of var N: Ys;

%Neighbourhood flattening annotation
annotation ls_neighbourhood;
annotation ls_dummy;
annotation ls_initialize(var bool: dummy_name);
annotation ls_defines_generator(var bool: dummy_name);
annotation ls_pre_condition(var bool: dummy_name);
annotation ls_post_condition(var bool: dummy_name);

%Moves
annotation swap_array(array[int] of var int: Xs1, var int: i, array[int] of var int: Xs2, var int: j);
annotation assign_array(array[int] of var int: Xs, var int: i, var int: v);
annotation and(array[int] of ann:moves);

annotation neighbourhood(array[int] of ann: neighbours);

function ann: circuit_neighbourhood(array [int] of var int: Xs) =
(let{
%Init
var bool: dummy :: ls_dummy; %needs to be unique for every instance of this neighbourhood -> which is it right?
constraint circuit(Xs) ::ls_initialize(dummy); 
} in let{
  %vars
  var index_set(Xs): p1 :: ls_defines_generator(dummy);
  var index_set(Xs): p2 :: ls_defines_generator(dummy);
  %where
  constraint (Xs[p1] != p2 /\ Xs[Xs[p1]] != p2) :: ls_pre_condition(dummy);
  }in let{
    %ensure
    %constraint true :: ls_post_condition(dummy_all_diff);
    constraint true;
    }in
    and([assign_array(Xs, p1, Xs[Xs[p1]]), assign_array(Xs, p2, Xs[p1]), assign_array(Xs, Xs[p1], Xs[p2])])) :: ls_neighbourhood; % element constraint introduced here is not annotated

solve :: neighbourhood([circuit_neighbourhood(Ys)])
satisfy;
