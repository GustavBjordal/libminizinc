include "ls-annotation.mzn";
include "globals.mzn";
set of int: N = 1..10;
set of int: V = 1..20;
array [N] of var V: Ys;
function ann: all_diff(array [int] of var int: Xs) :: neighbourhood_definition
     = 
    let {
        var bool: dummy, 
        
        var index_set(Xs): i :: ls_defines_generator(dummy), 
        var index_set(Xs): j :: ls_defines_generator(dummy),
        constraint i < j :: ls_pre_condition(dummy), 
    } in (
        let {constraint Xs[1] < Xs[max(index_set(Xs))]
     :: ls_post_condition(dummy),
        } in (
            neighbourhood_and(assign_array(Xs, i, Xs[j]), assign_array(Xs, j, Xs
    [i]))) :: new_constraint_context) :: new_constraint_context;
solve :: all_diff(Ys) satisfy;