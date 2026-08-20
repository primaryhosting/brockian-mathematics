import Mathlib
open Matrix
namespace C3.QI5

def CCX : Matrix (Fin 8) (Fin 8) ℂ := Matrix.of (fun i j => if (i=6∧j=7)∨(i=7∧j=6) then 1 else if i=j ∧ i≠6 ∧ i≠7 then 1 else 0)

/-- The Toffoli (CCX) gate is an involution. -/
