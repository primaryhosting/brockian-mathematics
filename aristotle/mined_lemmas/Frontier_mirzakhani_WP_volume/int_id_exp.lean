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

theorem int_id_exp (r : ℝ) (hr : 0 < r) :
    ∫ x in Ioi (0:ℝ), x * Real.exp (-(r * x)) = 1 / r ^ 2 := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 2) (r := r) (by norm_num) hr
  rw [Real.Gamma_two] at h
  have e : ∫ x in Ioi (0:ℝ), x * Real.exp (-(r * x))
      = ∫ t in Ioi (0:ℝ), t ^ ((2:ℝ) - 1) * Real.exp (-(r * t)) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    norm_num
  rw [e, h, mul_one, one_div]
  simp

/-- The alternating Basel series `∑ (-1)^n / (n+1)^2 = π^2/12`. -/
