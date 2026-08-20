import Mathlib
open Matrix Polynomial
namespace BrockianFrontier.PentagonSpectrum

/-- Adjacency matrix of the 5-cycle Cā‚… (the pentagon graph). -/

def C6 : Matrix (Fin 6) (Fin 6) ℝ :=
  !![0,1,0,0,0,1; 1,0,1,0,0,0; 0,1,0,1,0,0; 0,0,1,0,1,0; 0,0,0,1,0,1; 1,0,0,0,1,0]

/-- The eigenvalues of Cā‚™ are `2 cos(2Ļ€k/n)`. For the pentagon this pulls the spectrum
    into the golden-ratio field: `2 cos(2Ļ€/5) = (√5 āˆ’ 1)/2 = Ļ† āˆ’ 1` is an eigenvalue. -/
