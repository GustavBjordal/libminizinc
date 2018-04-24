include "globals.mzn";
include "local-search.mzn";
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

array [BINS] of var 0..maxCapa: load;
array [ITEMS] of var BINS: placed_in;
constraint bin_packing_load(load,placed_in,size);

 int: maxColors = 2;
 array[BINS] of var 0..maxColors: num_colors;
 
constraint forall( b in BINS)(
  num_colors[b] = sum( [ exists(i in ITEMS where color[i] = c)(placed_in[i] = b) | c in COLORS ]) 
);

array[0..maxCapa] of 0..maxCapa: slack =
  array1d(0..maxCapa,[min([s | s in capacities++[0] where s >= x]) - x | x in 0..maxCapa]);

var int: objective;
constraint objective = sum(i in BINS)(slack[load[i]]);

solve 
:: use_neighborhood([soft_packing(placed_in)]) 
minimize objective;

function ann: binpacking(array [int] of var int: placed) :: neighborhood_definition =
initially(
  forall(i in ITEMS)( placed[i] = i) /\
  forall(b in BINS)(num_colors[b] <= 2 )
)
/\
moves(i, j in ITEMS where i<j /\ placed[i] != placed[j] /\ (size[i] != size[j] \/ color[i] != color[j]) /\ (slack[load[placed[i]]] > 0 \/ slack[load[placed[j]]] > 0 ))
      (placed[i] :=: placed[j] /\
      ensuring(forall(b in BINS)(num_colors[b] <= maxColors))
      )
union
moves(i in ITEMS, b in BINS where placed[i] != b /\ slack[load[placed[i]]] > 0 
/\ (load[b]>0 \/ int_eq(b, min([(load[i] == 0)*i | i in BINS ]))) /\ size[i]+load[b] <= maxCapa)(
    placed[i] := b/\
      ensuring(forall(b in BINS)(num_colors[b] <= 2))
)
;

function ann: hard_packing(array [int] of var int: placed) :: neighborhood_definition =
initially(
forall(i in ITEMS)( int_eq(placed[i], i)) /\
forall(b in BINS)(num_colors[b] <= 2 )
)
/\
moves(i in ITEMS, b in BINS where slack[load[placed[i]]] > 0 
  /\ size[i]+load[b] <= maxCapa)
  (   
    placed[i] := b /\
    ensuring(forall(b in BINS)(num_colors[b] <= 2))
);

function ann: soft_packing(array [int] of var int: placed) :: neighborhood_definition =
initially(
forall(i in ITEMS)( int_eq(placed[i], i)) /\
forall(b in BINS)(num_colors[b] <= 2 )
)
/\
moves(i, j in ITEMS where i<j /\ placed[i] != placed[j] /\ (size[i] != size[j] \/ color[i] != color[j]) )
      (placed[i] :=: placed[j] )
union
moves(i in ITEMS, b in BINS where load[b]>0 /\ slack[load[placed[i]]] > 0 )(
    placed[i] := b 
);

