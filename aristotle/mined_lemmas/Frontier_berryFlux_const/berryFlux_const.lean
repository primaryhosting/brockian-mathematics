/-
# Tknn Chern Hall
Category: Frontier Physics
Target: Frontier.tknn_chern_hall
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Tknn Chern Hall
Category: Frontier Physics
Target: Frontier.tknn_chern_hall
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

/-- The (first) Chern number of a Bloch band with Berry curvature `F` on the Brillouin-zone
torus `[0, 2π] × [0, 2π]`: the integral of the Berry curvature divided by `2π`. -/

lemma berryFlux_const (n : ℤ) (F : ℝ → ℝ → ℝ)
    (hF : ∀ kx ky : ℝ, F kx ky = (n : ℝ) / (2 * Real.pi)) :
    (∫ kx in (0:ℝ)..(2 * Real.pi), ∫ ky in (0:ℝ)..(2 * Real.pi), F kx ky)
      = 2 * Real.pi * (n : ℝ) := by
  have hpi : (2 * Real.pi) ≠ 0 := by positivity
  have hinner : ∀ kx : ℝ,
      (∫ ky in (0:ℝ)..(2 * Real.pi), F kx ky) = (n : ℝ) := by
    intro kx
    simp only [hF]
    rw [intervalIntegral.integral_const, smul_eq_mul]
    field_simp
    ring
  rw [intervalIntegral.integral_congr (g := fun _ : ℝ => (n : ℝ))
    (fun kx _ => hinner kx), intervalIntegral.integral_const, smul_eq_mul]
  ring

/-- Quantization: if the total Berry flux through the Brillouin zone is `2π n` for an integer `n`,
then the Chern number is `n` and the Hall conductance is the integer multiple `n · e² / h`
of the conductance quantum. -/
