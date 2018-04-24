annotation new_constraint_context;
%Neighbourhood flattening annotation
annotation flat_function;
annotation void;
annotation defines_generator;
% annotation neighbourhood_or(ann: x, ann:y);
% annotation neighbourhood_or(array[int] of ann: X);
annotation neighborhood_and(ann: x, ann:y);
annotation neighborhood_and(array[int] of ann: X);
annotation use_neighborhood(array[int] of ann: X);
annotation use_neighborhood( ann: X);
annotation neighborhood_definition;
annotation neighborhood_declaration(array[int] of ann: neighborhoods,  ann: initially);
annotation neighborhood_declaration(array[int] of ann: neighborhoods);
%Moves
function ann: swap_array(array[int] of var int: Xs1, var int: i, array[int] of var int: Xs2, var int: j);
function ann: assign_array(array[int] of var int: Xs, var int: i, var int: v);
function ann: assign(var int, var int);
function ann: swap(var int, var int);

function ann: swap_array(array[int] of var bool: Xs1, var int: i, array[int] of var bool: Xs2, var int: j);
function ann: assign_array(array[int] of var bool: Xs, var int: i, var bool: v);
function ann: assign(var bool, var bool);
function ann: swap(var bool, var bool);

function ann: moves(array[int] of ann);
function ann: moves(array[int] of var opt ann);
function ann: initially(var bool);
function ann: initially(ann);
function ann: forall(array[int] of ann: X) = neighborhood_and(X);
function ann: '/\' (ann:x,ann:y);
function ann: '\/' (ann:x,ann:y);
function ann: 'union' (ann:x,ann:y);
function ann: ensuring(ann:e);

function ann: ':='(var int: lhs, var int: rhs);
function ann: ':=:'(var int: lhs, var int: rhs);