/-
# Willmore Conjecture
Category: Frontier — Fields Medal Work
Target: Frontier.willmore_conjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 does not allow a module docstring `/-! ... -/` before `import`; the header above is
-- therefore a plain block comment, and is repeated verbatim as a module docstring below.)

import Mathlib

/-!
# Willmore Conjecture
Category: Frontier — Fields Medal Work
Target: Frontier.willmore_conjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier

open Real intervalIntegral

/-! ## Vector algebra in `ℝ³`

We use `ℝ × ℝ × ℝ` as a model of `ℝ³` together with explicitly defined dot product,
cross product and Euclidean norm.  (The ambient `Prod` norm of Mathlib is the sup norm,
so we never use `‖·‖`; note that the notion of (Fréchet/one-variable) derivative does
not depend on the choice of an equivalent norm, so `deriv` below is the usual derivative
of an `ℝ³`-valued function.) -/

/-- Euclidean dot product on `ℝ³`. -/

lemma hasDerivAt_willmoreAntideriv {R r : ℝ} (hr : 0 < r) (hR : r < R) (u : ℝ) :
    HasDerivAt (fun t : ℝ =>
        (t - 2 * arctan (r * sin t / (R + Real.sqrt (R ^ 2 - r ^ 2) + r * cos t)))
          / Real.sqrt (R ^ 2 - r ^ 2))
      (1 / (R + r * cos u)) u := by
  have hR0 : 0 < R := lt_trans hr hR
  have hsq : 0 < R ^ 2 - r ^ 2 := by nlinarith
  obtain ⟨s, hs_def⟩ : ∃ s, s = Real.sqrt (R ^ 2 - r ^ 2) := ⟨_, rfl⟩
  have hs : 0 < s := hs_def ▸ Real.sqrt_pos.mpr hsq
  have hs2 : s ^ 2 = R ^ 2 - r ^ 2 := hs_def ▸ Real.sq_sqrt hsq.le
  rw [← hs_def]
  have hp : 0 < R + r * cos u := radial_pos hr hR
  have hDpos : 0 < R + s + r * cos u := by linarith
  have hDne : R + s + r * cos u ≠ 0 := ne_of_gt hDpos
  have hRs : (0:ℝ) < R + s := by linarith
  have hN : HasDerivAt (fun t : ℝ => r * sin t) (r * cos u) u := by
    simpa using (Real.hasDerivAt_sin u).const_mul r
  have hDd : HasDerivAt (fun t : ℝ => R + s + r * cos t) (-(r * sin u)) u := by
    simpa using ((Real.hasDerivAt_cos u).const_mul r).const_add (R + s)
  have hq := hN.div hDd hDne
  have harc := (hasDerivAt_arctan (r * sin u / (R + s + r * cos u))).comp u hq
  have h1 : HasDerivAt (fun t : ℝ => t) (1:ℝ) u := hasDerivAt_id u
  have hmain := (h1.sub (harc.const_mul 2)).div_const s
  convert hmain using 1
  have hsin := sin_sq_add_cos_sq u
  have h1p : 1 + (r * sin u / (R + s + r * cos u)) ^ 2
      = (2 * (R + s) * (R + r * cos u)) / (R + s + r * cos u) ^ 2 := by
    field_simp
    linear_combination r ^ 2 * hsin + hs2
  have hnum : r * cos u * (R + s + r * cos u) - r * sin u * -(r * sin u)
      = r * ((R + s) * cos u + r) := by linear_combination r ^ 2 * hsin
  rw [h1p, one_div_div, hnum]
  have hprod : (R + s + r * cos u) ^ 2 / (2 * (R + s) * (R + r * cos u))
        * (r * ((R + s) * cos u + r) / (R + s + r * cos u) ^ 2)
      = r * ((R + s) * cos u + r) / (2 * (R + s) * (R + r * cos u)) := by
    field_simp
  rw [hprod, eq_div_iff (ne_of_gt hs)]
  field_simp
  linear_combination hs2

