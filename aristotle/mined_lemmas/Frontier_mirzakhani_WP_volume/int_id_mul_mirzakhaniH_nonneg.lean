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

theorem int_id_mul_mirzakhaniH_nonneg (t : ℝ) (ht : 0 ≤ t) :
    (∫ x in Ioi (0:ℝ), x * mirzakhaniH x t) = t ^ 2 / 2 + 2 * Real.pi ^ 2 / 3 := by
  have hcont : Continuous (fun u : ℝ => u * wpPhi u) := continuous_id.mul continuous_wpPhi
  have hle : (-t : ℝ) ≤ t := by linarith
  -- split the kernel
  have hsplit : (∫ x in Ioi (0:ℝ), x * mirzakhaniH x t)
      = (∫ x in Ioi (0:ℝ), x * wpPhi (x + t)) + ∫ x in Ioi (0:ℝ), x * wpPhi (x + -t) := by
    rw [← integral_add (integrableOn_id_mul_wpPhi_shift t) (integrableOn_id_mul_wpPhi_shift (-t))]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x _
    show x * mirzakhaniH x t = x * wpPhi (x + t) + x * wpPhi (x + -t)
    unfold mirzakhaniH
    rw [show x - t = x + -t from by ring]
    ring
  -- the two shifted integrals
  have e1 := int_id_mul_wpPhi_shift t
  have e2 := int_id_mul_wpPhi_shift (-t)
  -- split the integrals over `Ioi (-t)` at `t`
  have s1 : (∫ u in Ioi (-t), u * wpPhi u)
      = (∫ u in (-t)..t, u * wpPhi u) + ∫ u in Ioi t, u * wpPhi u :=
    setIntegral_Ioi_split _ (-t) t hle hcont.integrableOn_Ioc (integrableOn_id_mul_wpPhi_Ioi t)
  have s2 : (∫ u in Ioi (-t), wpPhi u) = (∫ u in (-t)..t, wpPhi u) + ∫ u in Ioi t, wpPhi u :=
    setIntegral_Ioi_split _ (-t) t hle continuous_wpPhi.integrableOn_Ioc
      (integrableOn_wpPhi_Ioi t)
  have s3 : (∫ u in Ioi (0:ℝ), u * wpPhi u)
      = (∫ u in (0:ℝ)..t, u * wpPhi u) + ∫ u in Ioi t, u * wpPhi u :=
    setIntegral_Ioi_split _ 0 t ht hcont.integrableOn_Ioc (integrableOn_id_mul_wpPhi_Ioi t)
  have r1 := intervalIntegral_wpPhi_symm t
  have r2 := intervalIntegral_id_mul_wpPhi_symm t
  have hbase := int_id_mul_wpPhi
  rw [hsplit, e1, e2, s1, s2, r1, r2] at *
  rw [hbase] at s3
  linarith [s3]

/-- **Mirzakhani's kernel integral.**  For every `t`,
`∫_0^∞ x H(x,t) dx = t²/2 + 2π²/3`. -/
