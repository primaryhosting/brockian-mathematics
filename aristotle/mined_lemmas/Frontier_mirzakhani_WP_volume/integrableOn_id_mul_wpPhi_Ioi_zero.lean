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

theorem integrableOn_id_mul_wpPhi_Ioi_zero :
    IntegrableOn (fun u : ℝ => u * wpPhi u) (Ioi 0) := by
  have hg : IntegrableOn (fun u : ℝ => u * Real.exp (-((1/2) * u))) (Ioi 0) := by
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow (s := 1) (p := 1) (b := (1/2 : ℝ))
      (by norm_num) (le_refl 1) (by norm_num)
    apply h.congr_fun _ measurableSet_Ioi
    intro x hx
    simp [Real.rpow_one]
  have hmeas : Continuous (fun u : ℝ => u * wpPhi u) := continuous_id.mul continuous_wpPhi
  apply Integrable.mono' hg hmeas.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  simp only [mem_Ioi] at hu
  rw [Real.norm_eq_abs, abs_of_pos (mul_pos hu (wpPhi_pos u))]
  have h1 := wpPhi_le_exp u
  have h3 : u * wpPhi u ≤ u * Real.exp (-(u/2)) := by nlinarith [wpPhi_pos u]
  rw [show -((1/2 : ℝ) * u) = -(u/2) by ring]
  exact h3

