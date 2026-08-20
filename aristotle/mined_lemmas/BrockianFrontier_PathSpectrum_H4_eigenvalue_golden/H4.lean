import Mathlib
open Matrix Polynomial
namespace BrockianFrontier.PathSpectrum

/-- The 4-vertex path Hamiltonian: tridiagonal, 2 on the diagonal, -1 on each path edge.
    (Extends the verified H1, H2, H3 in the Constellation Spectrum.) -/

def H4 : Matrix (Fin 4) (Fin 4) ℝ :=
  !![2,-1,0,0; -1,2,-1,0; 0,-1,2,-1; 0,0,-1,2]

/-- The 5-vertex path Hamiltonian. -/
