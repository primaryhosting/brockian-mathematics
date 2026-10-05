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

theorem integrableOn_id_mul_wpPhi_Ioi (c : ℝ) :
    IntegrableOn (fun u : ℝ => u * wpPhi u) (Ioi c) := by
  rcases le_or_gt 0 c with h | h
  · exact integrableOn_id_mul_wpPhi_Ioi_zero.mono_set (Ioi_subset_Ioi h)
  · have h1 : IntegrableOn (fun u : ℝ => u * wpPhi u) (Ioc c 0) :=
      (continuous_id.mul continuous_wpPhi).integrableOn_Ioc
    have h2 := h1.union integrableOn_id_mul_wpPhi_Ioi_zero
    rwa [Ioc_union_Ioi_eq_Ioi h.le] at h2

