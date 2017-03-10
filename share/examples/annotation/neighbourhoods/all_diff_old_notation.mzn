include "globals.mzn";
set of int: N = 1..10;
set of int: V = 1..20;
array[N] of var V: Ys;

%Neighbourhood flattening annotation
annotation ls_dummy();
annotation ls_initialize(var bool: dummy_name);
annotation defines_generator(var bool: dummy_name);
annotation defines_where(var bool: dummy_name);
annotation defines_ensure(var bool: dummy_name);

%Moves
annotation swap_array(array[int] of var int: Xs1, var int: i, array[int] of var int: Xs2, var int: j);
annotation assign_array(array[int] of var int: Xs, var int: i, var int: v);

annotation neighbourhood(array[int] of ann: neighbours);

function ann: all_diff_part1(array [int] of var int: Xs) =
let{
%Init
var bool: dummy; %needs to be unique for every instance of this neighbourhood -> which is it right?
constraint all_different(Xs) :: ls_initialize(dummy) ; %This is eliminated by CSE but does not inherit both annotations.
} in let{
  %vars
  var index_set(Xs): i_comp1 :: defines_generator(dummy);
  var index_set(Xs): j_comp1 :: defines_generator(dummy);
  %where
  %This annotation goes missing
  constraint (i_comp1 < j_comp1) :: defines_where(dummy);
  }in let{
    %ensure
    %constraint true :: ls_post_condition(dummy);
    constraint true;
    }in
    swap_array(Xs,i_comp1,Xs,j_comp1);
    
function ann: all_diff_part2(array [int] of var int: Xs) =
let{
%Init
var bool: dummy;
constraint all_different(Xs) :: ls_initialize(dummy) ;
} in let{
  %vars
  var index_set(Xs): i_comp2 :: defines_generator(dummy);
  var dom_array(Xs): v_comp2 :: defines_generator(dummy);
  %where
  constraint  forall(j in index_set(Xs))(Xs[j] != v_comp2):: defines_where(dummy);
  %This does not work: /\  v in dom(Xs[i])
  }in let{
    %ensure
    %constraint true :: ls_post_condition(dummy);
    constraint true;
    }in
    assign_array(Xs,i_comp2,v_comp2) 
    ;

solve :: neighbourhood([all_diff_part1(Ys), all_diff_part2(Ys)])
satisfy;

% function array[int] of ann: all_diff(array [int] of var int: Xs) =
% let{
% %Init
% constraint all_different(Xs);
% } in let{
%   %vars
%   var dom_array(Xs): i;
%   var dom_array(Xs): j;
%   %where
%   constraint i <j;
%   }in let{
%     %ensure
%     constraint true;
%     }in
%     [swap_assign(Xs,i,Xs,j)];


%  from(i, j in N where i<j)(
%    Xs[i] :=: Xs[j]
%    ensure alldifferent(Xs) %Redundant
%  ) ++
%  from(i in N, v in V where forall(n in N)(Xs[n] != v))(
%    Xs[i] := v
%    ensure  alldifferent(Xs) %Redundant
%  ) :: cbls_initialize(alldifferent(Xs));

% solve :: cbls_search(tabu(10), random_nonworsening(alldiff_neighbourhood)))
%       satisfy


