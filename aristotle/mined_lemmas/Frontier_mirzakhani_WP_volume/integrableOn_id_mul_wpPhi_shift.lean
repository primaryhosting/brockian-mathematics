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

theorem integrableOn_id_mul_wpPhi_shift (s : ℝ) :
    IntegrableOn (fun x : ℝ => x * wpPhi (x + s)) (Ioi 0) := by
  have hg : IntegrableOn (fun u : ℝ => Real.exp (-(s/2)) * (u * Real.exp (-((1/2) * u))))
      (Ioi 0) := by
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow (s := 1) (p := 1) (b := (1/2 : ℝ))
      (by norm_num) (le_refl 1) (by norm_num)
    have h' : IntegrableOn (fun u : ℝ => u * Real.exp (-((1/2) * u))) (Ioi 0) := by
      apply h.congr_fun _ measurableSet_Ioi
      intro x hx
      simp [Real.rpow_one]
    exact h'.const_mul _
  have hmeas : Continuous (fun x : ℝ => x * wpPhi (x + s)) :=
    continuous_id.mul (continuous_wpPhi.comp (continuous_id.add continuous_const))
  apply Integrable.mono' hg hmeas.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  simp only [mem_Ioi] at hu
  rw [Real.norm_eq_abs, abs_of_pos (mul_pos hu (wpPhi_pos _))]
  have h1 : wpPhi (u + s) ≤ Real.exp (-((u+s)/2)) := wpPhi_le_exp _
  have h2 : Real.exp (-((u+s)/2)) = Real.exp (-(s/2)) * Real.exp (-((1/2) * u)) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [h2] at h1
  nlinarith [wpPhi_pos (u+s), Real.exp_pos (-(s/2)), Real.exp_pos (-((1/2)*u))]

