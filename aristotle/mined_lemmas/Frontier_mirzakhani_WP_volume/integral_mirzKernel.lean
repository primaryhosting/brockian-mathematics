/-
# Mirzakhani WP Volume
Category: Frontier — Fields Medal Work
Target: Frontier.mirzakhani_WP_volume
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Mirzakhani WP Volume
Category: Frontier — Fields Medal Work
Target: Frontier.mirzakhani_WP_volume
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

open MeasureTheory Set Real Asymptotics

namespace Frontier

/-! ## Mirzakhani's integration kernel -/

/-- The basic "logistic" profile appearing in Mirzakhani's kernels:
`logistic u = 1 / (1 + exp (u / 2))`. -/

lemma integral_mirzKernel (t : ℝ) :
    ∫ x in Ioi (0:ℝ), x * mirzKernel x t = t ^ 2 / 2 + 2 * π ^ 2 / 3 := by
  rcases le_or_gt 0 t with ht | ht
  · exact integral_mirzKernel_of_nonneg ht
  · have h := integral_mirzKernel_of_nonneg (t := -t) (by linarith)
    rw [show ((-t) ^ 2 : ℝ) = t ^ 2 by ring] at h
    rw [← h]
    exact setIntegral_congr_fun measurableSet_Ioi (fun x _ => by rw [mirzKernel_neg])

/-- `x ↦ x · H(x, s)` is integrable on the positive half-line. -/
