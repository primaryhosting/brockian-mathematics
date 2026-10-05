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

def deficiencySpace (q : ℝ → ℂ) (z : ℂ) : Submodule ℂ (ℝ → ℂ × ℂ) where
  carrier := {w | IsSolution q z w ∧ MemLp (fun t => (w t).1) 2 (volume.restrict (Set.Ioi 0))}
  add_mem' := by
    rintro w₁ w₂ ⟨hs₁, hL₁⟩ ⟨hs₂, hL₂⟩
    exact ⟨(solutionSpace q z).add_mem hs₁ hs₂, by simpa using hL₁.add hL₂⟩
  zero_mem' := ⟨(solutionSpace q z).zero_mem, by simp⟩
  smul_mem' := by
    rintro c w ⟨hs, hL⟩
    exact ⟨(solutionSpace q z).smul_mem c hs, by simpa using hL.const_smul c⟩

/-- Evaluation of a deficiency element at the base point `0`, recording the Cauchy data
`(u 0, u' 0)` of the underlying ODE solution. -/
