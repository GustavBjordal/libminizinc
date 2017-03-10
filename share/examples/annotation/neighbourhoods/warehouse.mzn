include "globals.mzn";
int: w = 5;
int: s = 10;
int: is_open_cost = 100;
set of int: O = {2,4};
array[1..w,1..s] of int: transportation_cost =
[|1,2,3,4,5,6,7,8,9,10
|1,2,3,4,5,6,7,8,9,10
|1,2,3,4,5,6,7,8,9,10
|1,2,3,4,5,6,7,8,9,10
|1,2,3,4,5,6,7,8,9,10|];
% Some decision variables omitted
array[1..w] of var bool: open;

annotation new_constraint_context;
%Neighbourhood flattening annotation
annotation ls_dummy();
annotation ls_initialize(var bool: dummy_name);
annotation ls_defines_generator(var bool: dummy_name);
annotation ls_pre_condition(var bool: dummy_name);
annotation ls_post_condition(var bool: dummy_name);

%Moves
annotation swap_array(array[int] of var int: Xs1, var int: i, array[int] of var int: Xs2, var int: j);
annotation assign_array(array[int] of var int: Xs, var int: i, var int: v);
annotation and(array[int] of ann:moves);

annotation neighbourhood(array[int] of ann: neighbours);

function ann: switch_status(array [int] of var int: status) =
(let{
%Init
var bool: dummy :: ls_dummy; %needs to be unique for every instance of this neighbourhood -> which is it right?
constraint true; %no init
} in (let{
  %vars
  var index_set(status): i :: ls_defines_generator(dummy);
  %where
  %This annotation goes missing
  constraint true;
  }in (let{
    %ensure
    %constraint true :: ls_post_condition(dummy_all_diff);
    constraint (exists(o in O)(status[o] = 1)) :: ls_post_condition(dummy);
    }in
    assign_array(status,i,1- status[i])):: new_constraint_context) :: new_constraint_context) :: new_constraint_context; % element & lin_eq constraint introduced here is not annotated
    
function ann: change_status(array [int] of var int: status) =
(let{
%Init
var bool: dummy:: ls_dummy; %needs to be unique for every instance of this neighbourhood -> which is it right?
constraint true; %no init
} in (let{
  %vars
  var index_set(status): i :: ls_defines_generator(dummy);
  var index_set(status): j :: ls_defines_generator(dummy);
  %where
  %This annotation goes missing
  constraint (i < j /\ status[i] != status[j]) :: ls_pre_condition(dummy);
  }in (let{
    %ensure
    %constraint (exists(o in O)(status[o] = 1)) :: ls_post_condition(dummy); % introduced variables do not inherit the annotation.
   % constraint (exists([status[o] = 1 | o in O])) :: ls_post_condition(dummy); % introduced variables do not inherit the annotation.
    constraint true;
    }in
    swap_array(status,i,status,j)):: new_constraint_context) :: new_constraint_context) :: new_constraint_context;
   % swap_array(status,i,status,j);

solve :: neighbourhood([switch_status(open), change_status(open)])
satisfy;