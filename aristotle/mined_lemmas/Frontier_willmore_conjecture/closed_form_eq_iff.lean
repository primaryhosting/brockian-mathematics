import Mathlib

/-!
# Willmore Conjecture
Category: Frontier — Fields Medal Work
Target: Frontier.willmore_conjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on the header: Lean 4 requires `import` commands to be the very first commands of a
file, so the module documentation block above is placed immediately after `import Mathlib`.
-/

open Real Set MeasureTheory intervalIntegral

namespace Frontier

/-! ## The torus of revolution and its Willmore energy

For `0 < r < R`, the torus of revolution `T R r ⊆ ℝ³` obtained by revolving the circle of
radius `r` centred at distance `R` from the axis is parametrised by

  `(θ, φ) ↦ ((R + r cos θ) cos φ, (R + r cos θ) sin φ, r sin θ)`,  `θ, φ ∈ [0, 2π]`.

Its two principal curvatures are `1 / r` (along the meridian circle) and
`cos θ / (R + r cos θ)` (along the parallel circle), and its area element is
`r (R + r cos θ) dθ dφ`.  These classical formulas are taken as the definitions below;
the Willmore energy `∫ H² dA` is then the honest double integral of the square of the mean
curvature against the area element.
-/

/-- The principal curvature `k₁ = 1/r` of the torus of revolution, along the meridian
circle of radius `r`. -/

theorem closed_form_eq_iff (hr : 0 < r) (hRr : r < R) :
    π ^ 2 * R ^ 2 / (r * Real.sqrt (R ^ 2 - r ^ 2)) = 2 * π ^ 2 ↔ R = Real.sqrt 2 * r := by
  set s := Real.sqrt (R ^ 2 - r ^ 2) with hs
  have hpos : 0 < R ^ 2 - r ^ 2 := by nlinarith
  have hs0 : 0 < s := Real.sqrt_pos.mpr hpos
  have hs2 : s ^ 2 = R ^ 2 - r ^ 2 := Real.sq_sqrt hpos.le
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h2p : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  rw [div_eq_iff (by positivity)]
  constructor
  · intro h
    have hR2 : R ^ 2 = 2 * r ^ 2 := by
      have hRs : R ^ 2 = 2 * (r * s) := by
        field_simp at h; nlinarith [pi_pos]
      nlinarith [sq_nonneg (R ^ 2 - 2 * r ^ 2)]
    have hfac : (R - Real.sqrt 2 * r) * (R + Real.sqrt 2 * r) = 0 := by nlinarith
    rcases mul_eq_zero.mp hfac with h' | h'
    · linarith
    · nlinarith
  · intro h
    subst h
    have hsq : (Real.sqrt 2 * r) ^ 2 = 2 * r ^ 2 := by nlinarith
    have hsr : s = r := by
      rw [hs, hsq, show 2 * r ^ 2 - r ^ 2 = r ^ 2 by ring, Real.sqrt_sq hr.le]
    rw [hsr, hsq]
    ring

end ClosedForm

/-- **The Willmore conjecture for tori of revolution** (Willmore's theorem, the base case of
the Willmore conjecture proved in full generality by Marques–Neves).

For every torus of revolution in `ℝ³` with radii `0 < r < R`, the Willmore energy
`∫ H² dA` is at least `2π²`, and equality holds exactly for the Clifford-type torus
`R = √2 · r`, the stereographic image of the Clifford torus. -/
