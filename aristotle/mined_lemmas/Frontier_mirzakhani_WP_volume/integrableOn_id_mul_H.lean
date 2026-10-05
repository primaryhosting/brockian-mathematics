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

theorem integrableOn_id_mul_H (t : ℝ) :
    IntegrableOn (fun x : ℝ => x * mirzakhaniH x t) (Ioi 0) := by
  have h1 := integrableOn_id_mul_wpPhi_shift t
  have h2 := integrableOn_id_mul_wpPhi_shift (-t)
  have h3 : IntegrableOn (fun x : ℝ => x * wpPhi (x + t) + x * wpPhi (x + -t)) (Ioi 0) :=
    h1.add h2
  apply MeasureTheory.IntegrableOn.congr_fun h3 _ measurableSet_Ioi
  intro x _
  show x * wpPhi (x + t) + x * wpPhi (x + -t) = x * mirzakhaniH x t
  unfold mirzakhaniH
  rw [show x - t = x + -t from by ring]
  ring

/-! ## The two basic definite integrals -/

