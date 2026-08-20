import Mathlib

/-!
# Brouwer 2 D
Category: Pure Mathematics
Target: Math.brouwer_2d
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Complex

namespace Math

/-- Algebraic identity: the positive root of `‖a + t v‖² = 1` (with `‖a‖ ≤ 1`, `v ≠ 0`)
is `t = (-⟪a,v⟫ + √(⟪a,v⟫² + ‖v‖²(1-‖a‖²)))/‖v‖²`. -/

theorem alg_root (ar ai vr vi : ℝ) (hN : 0 < vr ^ 2 + vi ^ 2) (hA : ar ^ 2 + ai ^ 2 ≤ 1) :
    (ar + ((-(ar * vr + ai * vi) +
        Real.sqrt ((ar * vr + ai * vi) ^ 2 + (vr ^ 2 + vi ^ 2) * (1 - (ar ^ 2 + ai ^ 2))))
        / (vr ^ 2 + vi ^ 2)) * vr) ^ 2
    + (ai + ((-(ar * vr + ai * vi) +
        Real.sqrt ((ar * vr + ai * vi) ^ 2 + (vr ^ 2 + vi ^ 2) * (1 - (ar ^ 2 + ai ^ 2))))
        / (vr ^ 2 + vi ^ 2)) * vi) ^ 2 = 1 := by
  set d := ar * vr + ai * vi with hd
  set N := vr ^ 2 + vi ^ 2 with hNdef
  set A := ar ^ 2 + ai ^ 2 with hAdef
  have hnn : 0 ≤ d ^ 2 + N * (1 - A) := by nlinarith [sq_nonneg d]
  set s := Real.sqrt (d ^ 2 + N * (1 - A)) with hsdef
  have hs : s ^ 2 = d ^ 2 + N * (1 - A) := Real.sq_sqrt hnn
  have hNne : N ≠ 0 := ne_of_gt hN
  field_simp
  nlinarith [hs, sq_nonneg (s - d), sq_nonneg N]

/-- There is no continuous retraction of the plane onto the unit circle:
if `r : ℂ → ℂ` is continuous with `‖r z‖ = 1` for all `z` and `r z = z` whenever `‖z‖ = 1`,
we get a contradiction.  The proof lifts `r` through the covering map
`Circle.exp : ℝ → Circle` (using that `ℂ` is simply connected) and computes winding numbers. -/
