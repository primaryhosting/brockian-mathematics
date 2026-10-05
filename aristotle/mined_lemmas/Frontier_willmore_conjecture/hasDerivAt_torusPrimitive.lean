/-
# Willmore Conjecture
Category: Frontier — Fields Medal Work
Target: Frontier.willmore_conjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
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

set_option pp.fullNames false
set_option pp.structureInstances true
set_option pp.coercions.types false
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

open Real

/-! ## Partial derivatives of functions of two real variables -/

/-- Partial derivative with respect to the first variable. -/

lemma hasDerivAt_torusPrimitive (hr : 0 < r) (hR : r < R) (u : ℝ) :
    HasDerivAt (torusPrimitive R r)
      ((R + 2 * r * cos u) ^ 2 / (4 * r * (R + r * cos u))) u := by
  set s := Real.sqrt (R ^ 2 - r ^ 2) with hs
  have hRr : 0 < R ^ 2 - r ^ 2 := by nlinarith
  have hs0 : 0 < s := Real.sqrt_pos.mpr hRr
  have hs2 : s ^ 2 = R ^ 2 - r ^ 2 := Real.sq_sqrt hRr.le
  have hw : 0 < R + r * cos u := by nlinarith [Real.neg_one_le_cos u, Real.cos_le_one u]
  have hD : 0 < R + s + r * cos u := by linarith
  have hN : HasDerivAt (fun t : ℝ => r * sin t) (r * cos u) u :=
    (Real.hasDerivAt_sin u).const_mul r
  have hDd : HasDerivAt (fun t : ℝ => R + s + r * cos t) (-(r * sin u)) u := by
    simpa using ((Real.hasDerivAt_cos u).const_mul r).const_add (R + s)
  have hq : HasDerivAt (fun t : ℝ => r * sin t / (R + s + r * cos t))
      ((r * cos u * (R + s + r * cos u) - r * sin u * (-(r * sin u)))
        / (R + s + r * cos u) ^ 2) u := hN.div hDd (ne_of_gt hD)
  have ha := (Real.hasDerivAt_arctan (r * sin u / (R + s + r * cos u))).comp u hq
  have h1 : HasDerivAt (fun t : ℝ => t - 2 * arctan (r * sin t / (R + s + r * cos t)))
      (1 - 2 * ((1 / (1 + (r * sin u / (R + s + r * cos u)) ^ 2)) *
        ((r * cos u * (R + s + r * cos u) - r * sin u * (-(r * sin u)))
          / (R + s + r * cos u) ^ 2))) u :=
    (hasDerivAt_id u).sub (ha.const_mul 2)
  have h2 := ((hN.const_mul 4).add (h1.const_mul (R ^ 2 / s))).const_mul (1 / (4 * r))
  have hkey := arctan_deriv_identity (R := R) (r := r) (s := s) (c := cos u) (sn := sin u)
    hr hR hs0 hs2 (Real.sin_sq_add_cos_sq u) hw
  rw [hkey] at h2
  have hval : 1 / (4 * r) * (4 * (r * cos u) + R ^ 2 / s * (s / (R + r * cos u)))
      = (R + 2 * r * cos u) ^ 2 / (4 * r * (R + r * cos u)) := by
    field_simp
    ring
  rw [hval] at h2
  exact h2

