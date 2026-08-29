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

namespace Frontier

open MeasureTheory Set Real

/-! ## Mirzakhani's integration kernel

Mirzakhani's recursion for Weil–Petersson volumes of moduli spaces of bordered
hyperbolic surfaces is driven by the kernel

`H (x, t) = 1 / (1 + exp ((x + t) / 2)) + 1 / (1 + exp ((x - t) / 2))`.

We write `wpPhi u = 1 / (1 + exp (u / 2))`, so that `H (x, t) = wpPhi (x+t) + wpPhi (x-t)`.
-/

/-- The basic Fermi–Dirac type profile `u ↦ 1 / (1 + e^{u/2})` out of which Mirzakhani's
integration kernel is built. -/

theorem int_id_mul_mirzakhaniH (t : ℝ) :
    (∫ x in Ioi (0:ℝ), x * mirzakhaniH x t) = t ^ 2 / 2 + 2 * Real.pi ^ 2 / 3 := by
  rcases le_or_gt 0 t with h | h
  · exact int_id_mul_mirzakhaniH_nonneg t h
  · have heven : ∀ x : ℝ, mirzakhaniH x t = mirzakhaniH x (-t) := by
      intro x
      unfold mirzakhaniH
      rw [show x + -t = x - t from by ring, show x - -t = x + t from by ring, add_comm]
    have : (∫ x in Ioi (0:ℝ), x * mirzakhaniH x t) = ∫ x in Ioi (0:ℝ), x * mirzakhaniH x (-t) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x _
      show x * mirzakhaniH x t = x * mirzakhaniH x (-t)
      rw [heven x]
    rw [this, int_id_mul_mirzakhaniH_nonneg (-t) (by linarith)]
    ring

/-- The `(0,4)` recursion involves the kernel evaluated at `L₁ + L_k` and `L₁ - L_k`,
weighted by the pair-of-pants volume `V_{0,3} = 1`. -/
