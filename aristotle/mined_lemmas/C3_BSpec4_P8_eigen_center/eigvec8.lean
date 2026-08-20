import Mathlib
open Matrix Polynomial
namespace C3.BSpec4

noncomputable def eigvec8 : Fin 8 → ℝ := fun i => Real.sin (((i : ℝ) + 1) * (Real.pi / 9))

/-- Three-term recurrence satisfied by `t ↦ sin t` with step `π/9`. -/
