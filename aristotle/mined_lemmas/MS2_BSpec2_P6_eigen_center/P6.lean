import Mathlib
open Matrix Polynomial
namespace MS2.BSpec2

def P6 : Matrix (Fin 6) (Fin 6) ℝ := !![2,-1,0,0,0,0; -1,2,-1,0,0,0; 0,-1,2,-1,0,0; 0,0,-1,2,-1,0; 0,0,0,-1,2,-1; 0,0,0,0,-1,2]

/-- `2 - 2·cos(π/7)` is an eigenvalue of the path Laplacian-type matrix `P6`.
The witnessing eigenvector is `v i = sin((i+1)·π/7)`; the row identities follow from
`sin(x) + sin(x + 2t) = 2·cos t·sin(x + t)` together with `sin(7·π/7) = sin π = 0`. -/
