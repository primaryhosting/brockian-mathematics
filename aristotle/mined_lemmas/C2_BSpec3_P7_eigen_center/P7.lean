import Mathlib
open Matrix Polynomial
namespace C2.BSpec3

def P7 : Matrix (Fin 7) (Fin 7) ℝ :=
  !![2,-1,0,0,0,0,0;-1,2,-1,0,0,0,0;0,-1,2,-1,0,0,0;0,0,-1,2,-1,0,0;0,0,0,-1,2,-1,0;0,0,0,0,-1,2,-1;0,0,0,0,0,-1,2]

set_option maxHeartbeats 1000000 in
/-- `2` is an eigenvalue of the path-graph Laplacian-type matrix `P7`: the matrix
`2 • 1 - P7` is the adjacency matrix of the path on 7 vertices, which is singular
because `(1,0,-1,0,1,0,-1)` lies in its kernel. -/
