include "globals.mzn";
include "ls-annotation.mzn";

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



nItems = 5;
ITEMS = 1..nItems;
BINS = 1..nItems;
COLORS = 1..max(privateColor);
CAPACITIES  = 1..20;

capacities = [12, 14, 17, 18, 19, 20, 23, 24, 25, 26, 27, 28, 29, 30, 32, 35, 39, 42, 43, 44];
size = [privateSize[i] | i in ITEMS];
color = [privateColor[i] | i in ITEMS];

array[int] of int: privateSize = [4, 22, 9, 5, 8, 3, 3, 4, 7, 7, 3, 2, 2, 8, 5, 7, 4, 7, 5, 7, 8, 3, 25, 14, 3, 22, 19, 19, 22, 22, 22, 20, 22, 5, 4, 10, 26, 17, 20, 16, 10, 19, 10, 10, 23, 22, 26, 27, 22, 27, 22, 22, 13, 14, 16, 26, 26, 27, 22, 20, 26, 22, 13, 19, 20, 16, 15, 17, 10, 20, 5, 26, 19, 15, 10, 10, 13, 13, 13, 12, 12, 18, 10, 18, 16, 20, 12, 6, 6, 15, 15, 15, 21, 30, 30, 30, 30, 23, 15, 15, 27, 27, 27, 27, 27, 27, 27, 27, 27, 10, 3];

array[int] of int: privateColor = [1, 2, 3, 4, 5, 6, 4, 7, 4, 8, 6, 6, 4, 9, 10, 11, 7, 11, 10, 11, 9, 1, 12, 13, 6, 14, 15, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 27, 34, 42, 35, 36, 43, 24, 44, 45, 46, 47, 48, 49, 50, 28, 51, 52, 24, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 68, 69, 70, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 79, 85, 86, 87, 88];