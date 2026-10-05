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

theorem intervalIntegral_id_mul_wpPhi_symm (t : ℝ) :
    (∫ u in (-t)..t, u * wpPhi u) = 2 * (∫ u in (0:ℝ)..t, u * wpPhi u) - t ^ 2 / 2 := by
  have hcont : Continuous (fun u : ℝ => u * wpPhi u) := continuous_id.mul continuous_wpPhi
  have hsplit : (∫ u in (-t)..t, u * wpPhi u)
      = (∫ u in (-t)..(0:ℝ), u * wpPhi u) + ∫ u in (0:ℝ)..t, u * wpPhi u := by
    rw [intervalIntegral.integral_add_adjacent_intervals]
    · exact hcont.intervalIntegrable _ _
    · exact hcont.intervalIntegrable _ _
  have hrefl : (∫ u in (-t)..(0:ℝ), u * wpPhi u) = ∫ u in (0:ℝ)..t, (-u) * wpPhi (-u) := by
    rw [intervalIntegral.integral_comp_neg (fun u => u * wpPhi u)]
    simp
  have hpt : ∀ u : ℝ, (-u) * wpPhi (-u) = u * wpPhi u - u := by
    intro u
    have h0 := wpPhi_add_neg u
    have h : wpPhi (-u) = 1 - wpPhi u := by linarith
    rw [h]; ring
  have hsub : (∫ u in (0:ℝ)..t, (u * wpPhi u - u))
      = (∫ u in (0:ℝ)..t, u * wpPhi u) - ∫ u in (0:ℝ)..t, u :=
    intervalIntegral.integral_sub (hcont.intervalIntegrable _ _)
      (continuous_id.intervalIntegrable _ _)
  rw [hsplit, hrefl]
  simp only [hpt]
  rw [hsub, integral_id]
  ring

/-- Splitting an integral over `Ioi a` at a point `b ≥ a`. -/
