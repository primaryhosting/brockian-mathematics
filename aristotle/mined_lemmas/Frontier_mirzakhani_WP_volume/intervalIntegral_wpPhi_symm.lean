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

theorem intervalIntegral_wpPhi_symm (t : ℝ) :
    (∫ u in (-t)..t, wpPhi u) = t := by
  have hint1 : IntervalIntegrable (fun u : ℝ => wpPhi (-u)) volume 0 t :=
    (continuous_wpPhi.comp continuous_neg).intervalIntegrable _ _
  have hint2 : IntervalIntegrable wpPhi volume 0 t := continuous_wpPhi.intervalIntegrable _ _
  have hsplit : (∫ u in (-t)..t, wpPhi u)
      = (∫ u in (-t)..(0:ℝ), wpPhi u) + ∫ u in (0:ℝ)..t, wpPhi u := by
    rw [intervalIntegral.integral_add_adjacent_intervals]
    · exact continuous_wpPhi.intervalIntegrable _ _
    · exact continuous_wpPhi.intervalIntegrable _ _
  have hrefl : (∫ u in (-t)..(0:ℝ), wpPhi u) = ∫ u in (0:ℝ)..t, wpPhi (-u) := by
    rw [intervalIntegral.integral_comp_neg (fun u => wpPhi u)]
    simp
  have hadd : (∫ u in (0:ℝ)..t, wpPhi (-u)) + ∫ u in (0:ℝ)..t, wpPhi u
      = ∫ u in (0:ℝ)..t, (wpPhi (-u) + wpPhi u) :=
    (intervalIntegral.integral_add hint1 hint2).symm
  have hone : ∀ u : ℝ, wpPhi (-u) + wpPhi u = 1 := by
    intro u; rw [add_comm]; exact wpPhi_add_neg u
  rw [hsplit, hrefl, hadd]
  simp only [hone]
  simp

/-- Reflection for the weighted kernel: `∫_{-t}^{t} u φ(u) du = 2 ∫_0^t u φ(u) du - t²/2`. -/
