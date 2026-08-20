import Mathlib
open Matrix Polynomial
namespace C5.BSp6

noncomputable def v10 : Fin 10 → ℝ := fun i => Real.sin (((i : ℕ) + 1) * (Real.pi / 11))

/-- The three-term recurrence `sin(aθ) + sin((a+2)θ) = 2 cos θ · sin((a+1)θ)` for `θ = π/11`. -/
