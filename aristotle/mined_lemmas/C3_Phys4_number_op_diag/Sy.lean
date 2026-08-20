import Mathlib
open Matrix
namespace C3.Phys4
-- `noncomputable` added: `Real.sqrt` has no executable code.

def Sy : Matrix (Fin 2) (Fin 2) ℂ := !![0,-Complex.I;Complex.I,0]
