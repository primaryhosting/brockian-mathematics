import Mathlib
open Matrix
namespace C4.QC6

noncomputable def T : Matrix (Fin 2) (Fin 2) ℂ := !![1,0;0,Complex.exp (Complex.I*Real.pi/4)]
