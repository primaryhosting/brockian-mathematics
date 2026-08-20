import Mathlib
open Matrix
namespace C3.Phys4
-- `noncomputable` added: `Real.sqrt` has no executable code.

noncomputable def a : Matrix (Fin 3) (Fin 3) ℝ := !![0,1,0;0,0,Real.sqrt 2;0,0,0]
