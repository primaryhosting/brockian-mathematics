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

lemma arctan_deriv_identity {s c sn : ℝ} (hr : 0 < r) (hR : r < R) (hs0 : 0 < s)
    (hs2 : s ^ 2 = R ^ 2 - r ^ 2) (hsc : sn ^ 2 + c ^ 2 = 1) (hw : 0 < R + r * c) :
    1 - 2 * ((1 / (1 + (r * sn / (R + s + r * c)) ^ 2)) *
      ((r * c * (R + s + r * c) - r * sn * (-(r * sn))) / (R + s + r * c) ^ 2))
      = s / (R + r * c) := by
  have hD : 0 < R + s + r * c := by linarith
  have hK : 0 < 2 * (R + s) * (R + r * c) := by nlinarith
  have h1 : 1 + (r * sn / (R + s + r * c)) ^ 2
      = (2 * (R + s) * (R + r * c)) / (R + s + r * c) ^ 2 := by
    field_simp
    linear_combination hs2 + r ^ 2 * hsc
  have h1' : 1 / (1 + (r * sn / (R + s + r * c)) ^ 2)
      = (R + s + r * c) ^ 2 / (2 * (R + s) * (R + r * c)) := by
    rw [h1, one_div_div]
  rw [h1']
  have hstep : (R + s + r * c) ^ 2 / (2 * (R + s) * (R + r * c)) *
      ((r * c * (R + s + r * c) - r * sn * (-(r * sn))) / (R + s + r * c) ^ 2)
      = (r * c * (R + s) + r ^ 2) / (2 * (R + s) * (R + r * c)) := by
    rw [div_mul_div_comm, div_eq_div_iff (by positivity) (by positivity)]
    ring_nf
    linear_combination (r ^ 2 * (R + s + r * c) ^ 2 * (2 * (R + s) * (R + r * c))) * hsc
  rw [hstep]
  have hRs : (R + s) ≠ 0 := by nlinarith
  have hw' : (R + r * c) ≠ 0 := ne_of_gt hw
  field_simp
  linear_combination -hs2

