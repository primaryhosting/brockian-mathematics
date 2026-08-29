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

theorem int_id_mul_wpPhi_shift (s : ℝ) :
    (∫ x in Ioi (0:ℝ), x * wpPhi (x + s))
      = (∫ u in Ioi s, u * wpPhi u) - s * ∫ u in Ioi s, wpPhi u := by
  have h1 : (∫ x in Ioi (0:ℝ), x * wpPhi (x + s))
      = ∫ x in Ioi (0:ℝ), ((fun y : ℝ => (y - s) * wpPhi y) (x + s)) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    simp only []
    ring_nf
  rw [h1, setIntegral_Ioi_comp_add (fun y : ℝ => (y - s) * wpPhi y) 0 s, zero_add]
  have h2 : ∀ y : ℝ, (y - s) * wpPhi y = y * wpPhi y - s * wpPhi y := by intro y; ring
  simp only [h2]
  rw [integral_sub (integrableOn_id_mul_wpPhi_Ioi s) ((integrableOn_wpPhi_Ioi s).const_mul s),
    integral_const_mul]

/-- Reflection: `∫_{-t}^{t} φ = t`. -/
