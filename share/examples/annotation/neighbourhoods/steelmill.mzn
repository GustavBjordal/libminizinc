include "globals.mzn";
include "ls-annotation.mzn";
include "data.mzn";

int: nItems;
set of int: ITEMS;
set of int: BINS;
set of int: COLORS ;
set of int: CAPACITIES ;

array [CAPACITIES] of int: capacities;
array [ITEMS] of int: size;
array [ITEMS] of COLORS: color;
int: maxCapa = max(capacities);

array [BINS] of var 0..200: load;
array [ITEMS] of var BINS: placed_in;
constraint bin_packing_load(load,placed_in,size);

array [BINS,COLORS] of var 0..1: contains_color;

% constraint forall(b in BINS, c in COLORS)(
%   contains_color[b,c] = exists(i in ITEMS)(placed_in[i] = b /\ color[i] = c) 
% );

% constraint forall(i in ITEMS)(
%   contains_color[placed_in[i],color[i]] = 1
% );

array [BINS] of var int: num_colors =
	[sum([contains_color[b,c] | c in COLORS]) | b in BINS];
constraint forall(b in BINS)(num_colors[b] <= 2);

array[1..maxCapa+1] of 0..maxCapa: slack =
  [min([s | s in capacities++[0] where s >= x]) - x | x in 0..maxCapa];

var int: objective;
constraint objective = sum(i in BINS)(slack[load[i]+1]);

solve 
:: neighbourhood_and([binpacking(placed_in)]) 
minimize objective;

function ann: binpacking(array [int] of var int: placed) :: neighbourhood_definition =
initialize(forall(i in index_set(placed))(placed[i] = i) /\
forall(i in ITEMS)(
  contains_color[placed_in[i],color[i]] = 1
) /\
forall(b in BINS)(num_colors[b] = 1)/\
contains_color[2,1] = 1
)
/\
% from(i, j in ITEMS where i<j /\ (size[i] != size[j] \/ color[i] != color[j]) )
%       (placed[i] :=: placed[j] /\
%       ensure(forall(b in BINS)(num_colors[b] <= 2) /\ load[placed[i]] <= maxCapa /\ load[placed[j]] <= maxCapa )
      
%       )
% \/
from(i in ITEMS, b in BINS where (load[b]>0 \/ b = min([(load[i] == 0)*i | i in BINS ])) /\ size[i]+load[b] <= maxCapa)(
  placed[i] := b/\
  contains_color[placed_in[i],color[i]] := (sum(k in ITEMS)(placed_in[k] = placed_in[i] /\ k != i) > 0) /\
  contains_color[b,color[i]] := 1 /\  
      ensure(forall(b in BINS)(num_colors[b] <= 2))
);



