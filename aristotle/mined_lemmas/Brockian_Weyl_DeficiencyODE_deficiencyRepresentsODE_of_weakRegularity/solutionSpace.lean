import Mathlib

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

import Mathlib

/-!
# Deficiency Represents ODE Of Weak Regularity
Category: Brockian (Literature Discharge)
Target: Brockian.Weyl.DeficiencyODE.deficiencyRepresentsODE_of_weakRegularity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Classical

open Set MeasureTheory

namespace Brockian.Weyl.DeficiencyODE

/-- **Weak regularity** of a potential `q : ℝ → ℂ`: `q` is bounded on every compact interval.
This is much weaker than continuity of `q`; it is exactly what is needed to run the Gronwall
argument behind uniqueness for the Sturm–Liouville system. -/

def solutionSpace (q : ℝ → ℂ) (z : ℂ) : Submodule ℂ (ℝ → ℂ × ℂ) where
  carrier := {w | IsSolution q z w}
  add_mem' := by
    intro w₁ w₂ h₁ h₂ t
    have := (h₁ t).add (h₂ t)
    convert this using 1
    simp [Prod.ext_iff]
    ring
  zero_mem' := by
    intro t
    simpa using (hasDerivAt_const t (0 : ℂ × ℂ))
  smul_mem' := by
    intro c w h t
    have := (h t).const_smul c
    convert this using 1
    simp [Prod.ext_iff, Prod.smul_def]
    ring

/-- The **deficiency space** of the Sturm–Liouville expression at the spectral parameter `z`,
on the half line `(0, ∞)`: the solutions of the ODE whose first component is square integrable.
By Weyl's theory this is the space representing `ker (T* - z)` for the minimal operator `T`. -/
