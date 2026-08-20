import Mathlib
open Matrix Polynomial
namespace MS2.BSpec2

def C7 : Matrix (Fin 7) (Fin 7) ℝ := Matrix.of (fun i j => if (i-j = 1 ∨ j-i = 1 ∨ (i=0∧j=6) ∨ (i=6∧j=0)) then 1 else 0)
