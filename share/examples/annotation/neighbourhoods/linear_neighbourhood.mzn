include "globals.mzn";

set of int: N = 1..10;
set of int: V = 2..20;
array[N] of var V: Ys;
var int: T;

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
annotation assign(var int: x, var int: v);
annotation and(array[int] of ann:moves);

annotation neighbourhood(array[int] of ann: neighbours);

function ann: linear_neighbourhood_part1(array [int] of var int: Xs, var int: S) =
(let{
%Init
var bool: dummy :: ls_dummy; %needs to be unique for every instance of this neighbourhood -> which is it right?
constraint (sum(Xs) = S)  ::ls_initialize(dummy); 
} in let{
  %vars
  var index_set(Xs): p1 :: ls_defines_generator(dummy);
  var index_set(Xs): p2 :: ls_defines_generator(dummy);
  var -max(dom_array(Xs))..max(dom_array(Xs)): v :: ls_defines_generator(dummy);
  %where
  constraint (p1 != p2) :: ls_pre_condition(dummy);
  }in let{
    %ensure
    %constraint true :: ls_post_condition(dummy_all_diff);
    constraint true;
    }in
    and([assign_array(Xs, p1, Xs[p2] + v), assign_array(Xs, p2, Xs[p1] -v)])) :: ls_neighbourhood; % element constraint introduced here is not annotated

function ann: linear_neighbourhood_part2(array [int] of var int: Xs, var int: S) =
(let{
%Init
var bool: dummy :: ls_dummy; %needs to be unique for every instance of this neighbourhood -> which is it right?
constraint (sum(Xs) = S)  ::ls_initialize(dummy); 
} in let{
  %vars
  var index_set(Xs): p1 :: ls_defines_generator(dummy);
  var -max(dom_array(Xs))..max(dom_array(Xs)): v :: ls_defines_generator(dummy);
  %where
  constraint true;
  }in let{
    %ensure
    %constraint true :: ls_post_condition(dummy_all_diff);
    constraint true;
    }in
    and([assign_array(Xs, p1, Xs[p1] + v), assign(S, S+v)])) :: ls_neighbourhood; % element constraint introduced here is not annotated


solve :: neighbourhood([linear_neighbourhood_part1(Ys,T), linear_neighbourhood_part2(Ys,T)])
satisfy;
