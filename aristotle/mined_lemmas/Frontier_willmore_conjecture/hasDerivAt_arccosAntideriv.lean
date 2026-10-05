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

lemma hasDerivAt_arccosAntideriv (hr : 0 < r) (hRr : r < R) {θ : ℝ} (h0 : 0 < θ) (hπ : θ < π) :
    HasDerivAt (arccosAntideriv R r) ((R + r * Real.cos θ)⁻¹) θ := by
  have hD : 0 < R + r * Real.cos θ := add_mul_cos_pos hr hRr θ
  have hsin : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi h0 hπ
  have hd2 : 0 < R ^ 2 - r ^ 2 := by nlinarith
  have hq : 0 < Real.sqrt (R ^ 2 - r ^ 2) := Real.sqrt_pos.mpr hd2
  have hq2 : Real.sqrt (R ^ 2 - r ^ 2) ^ 2 = R ^ 2 - r ^ 2 := Real.sq_sqrt hd2.le
  have hpyth : Real.sin θ ^ 2 + Real.cos θ ^ 2 = 1 := Real.sin_sq_add_cos_sq θ
  set u : ℝ := (r + R * Real.cos θ) / (R + r * Real.cos θ) with hu
  have hone : 1 - u ^ 2 = (R ^ 2 - r ^ 2) * Real.sin θ ^ 2 / (R + r * Real.cos θ) ^ 2 := by
    rw [hu]; field_simp; nlinarith [hpyth]
  have hsqrt : Real.sqrt (1 - u ^ 2)
      = Real.sqrt (R ^ 2 - r ^ 2) * Real.sin θ / (R + r * Real.cos θ) := by
    rw [hone, show (R ^ 2 - r ^ 2) * Real.sin θ ^ 2 / (R + r * Real.cos θ) ^ 2
        = (Real.sqrt (R ^ 2 - r ^ 2) * Real.sin θ / (R + r * Real.cos θ)) ^ 2 by
      field_simp; nlinarith [hq2]]
    exact Real.sqrt_sq (by positivity)
  have hlt : u ^ 2 < 1 := by
    have : 0 < 1 - u ^ 2 := by rw [hone]; positivity
    linarith
  have hne1 : u ≠ 1 := by intro h; rw [h] at hlt; norm_num at hlt
  have hne2 : u ≠ -1 := by intro h; rw [h] at hlt; norm_num at hlt
  have hn : HasDerivAt (fun θ : ℝ => r + R * Real.cos θ) (R * (-Real.sin θ)) θ := by
    simpa using ((Real.hasDerivAt_cos θ).const_mul R).const_add r
  have hdd : HasDerivAt (fun θ : ℝ => R + r * Real.cos θ) (r * (-Real.sin θ)) θ := by
    simpa using ((Real.hasDerivAt_cos θ).const_mul r).const_add R
  have hU : HasDerivAt (fun θ : ℝ => (r + R * Real.cos θ) / (R + r * Real.cos θ))
      ((R * (-Real.sin θ) * (R + r * Real.cos θ) - (r + R * Real.cos θ) * (r * (-Real.sin θ)))
        / (R + r * Real.cos θ) ^ 2) θ := hn.div hdd hD.ne'
  have hA := (Real.hasDerivAt_arccos hne2 hne1).comp θ hU
  have hfin := hA.div_const (Real.sqrt (R ^ 2 - r ^ 2))
  convert hfin using 1
  rw [hsqrt]
  field_simp
  nlinarith [hq2, hq, hsin, hD]

