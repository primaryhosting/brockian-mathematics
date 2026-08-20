import Mathlib
open Matrix Polynomial
namespace BrockianFrontier.PathSpectrum

/-- The 4-vertex path Hamiltonian: tridiagonal, 2 on the diagonal, -1 on each path edge.
    (Extends the verified H1, H2, H3 in the Constellation Spectrum.) -/

def H5 : Matrix (Fin 5) (Fin 5) ℝ :=
  !![2,-1,0,0,0; -1,2,-1,0,0; 0,-1,2,-1,0; 0,0,-1,2,-1; 0,0,0,-1,2]

set_option maxHeartbeats 2000000 in
/-- The n-vertex path Hamiltonian has eigenvalues `2 - 2 cos (k π /(n+1))`.
    For H4 the smallest eigenvalue `2 - 2 cos (π/5)` lives in the golden-ratio field:
    prove it is a root of the characteristic polynomial. -/
