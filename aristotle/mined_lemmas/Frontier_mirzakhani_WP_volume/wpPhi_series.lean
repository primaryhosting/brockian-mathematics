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

theorem wpPhi_series (u : ℝ) (hu : 0 < u) :
    wpPhi u = ∑' n : ℕ, (-1:ℝ) ^ n * Real.exp (-(((n:ℝ) + 1) / 2 * u)) := by
  unfold wpPhi
  have hr : ‖(-Real.exp (-(u / 2)))‖ < 1 := by
    rw [norm_neg, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_lt_one_iff]
    linarith
  have hg := hasSum_geometric_of_norm_lt_one hr
  have h2 := hg.mul_left (Real.exp (-(u / 2)))
  have he : (fun n : ℕ => Real.exp (-(u / 2)) * (-Real.exp (-(u / 2))) ^ n)
      = fun n : ℕ => (-1:ℝ) ^ n * Real.exp (-(((n:ℝ) + 1) / 2 * u)) := by
    funext n
    have h1 : Real.exp (-(u / 2)) * Real.exp ((n:ℝ) * -(u / 2))
        = Real.exp (-(((n:ℝ) + 1) / 2 * u)) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [neg_pow, ← Real.exp_nat_mul, ← mul_assoc, mul_comm (Real.exp (-(u / 2))) ((-1:ℝ) ^ n),
      mul_assoc, h1]
  rw [he] at h2
  rw [h2.tsum_eq, Real.exp_neg]
  have hp : (0:ℝ) < Real.exp (u / 2) := Real.exp_pos _
  field_simp
  rw [show Real.exp (u / 2) - -1 = 1 + Real.exp (u / 2) from by ring, div_self (by positivity)]

/-- The key definite integral: `∫_0^∞ u / (1 + e^{u/2}) du = π²/3`. -/
