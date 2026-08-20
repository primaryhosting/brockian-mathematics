import Mathlib
open Matrix Polynomial
namespace BrockianFrontier.PentagonSpectrum

/-- Adjacency matrix of the 5-cycle Cā‚… (the pentagon graph). -/

def C5 : Matrix (Fin 5) (Fin 5) ℝ :=
  !![0,1,0,0,1; 1,0,1,0,0; 0,1,0,1,0; 0,0,1,0,1; 1,0,0,1,0]

/-- The 6-cycle Cā‚† adjacency matrix. -/
