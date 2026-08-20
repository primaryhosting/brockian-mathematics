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

lemma tknn_of_flux (e h : ℝ) (n : ℤ) (F : ℝ → ℝ → ℝ)
    (hflux : (∫ kx in (0:ℝ)..(2 * Real.pi), ∫ ky in (0:ℝ)..(2 * Real.pi), F kx ky)
      = 2 * Real.pi * (n : ℝ)) :
    chernNumber F = (n : ℝ) ∧ hallConductance e h F = (n : ℝ) * (e ^ 2 / h) := by
  have hpi : (2 * Real.pi) ≠ 0 := by positivity
  have hchern : chernNumber F = (n : ℝ) := by
    unfold chernNumber
    rw [hflux]
    field_simp
  exact ⟨hchern, by unfold hallConductance; rw [hchern]; ring⟩

/-- **TKNN / integer quantum Hall effect (base case).**

For a Bloch band whose Berry curvature over the Brillouin zone is the constant `n / (2π)`
(so that the total Berry flux through the torus is `2π n`), the first Chern number equals the
integer `n`, and the Hall conductance is exactly `n · e² / h`, i.e. an integer multiple of the
conductance quantum. -/
