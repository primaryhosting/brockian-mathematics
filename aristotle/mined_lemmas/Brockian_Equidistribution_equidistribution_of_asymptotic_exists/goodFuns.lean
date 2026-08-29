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
# Equidistribution Of Asymptotic Exists
Category: Brockian (Open Discharge)
Target: Brockian.Equidistribution.equidistribution_of_asymptotic_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(Note: this Lean toolchain requires `import` to be the very first command in a file, so the
required header comment appears immediately after the import.)
-/

open Filter MeasureTheory Set Topology
open scoped ENNReal NNReal Real BigOperators

namespace Brockian.Equidistribution

/-- The circle `ℝ / ℤ`, on which we study equidistribution. -/
abbrev Circ : Type := AddCircle (1 : ℝ)

noncomputable instance : IsProbabilityMeasure (volume : Measure Circ) := ⟨by simp⟩

/-- Continuous functions on the (compact) circle are integrable for any finite measure. -/

noncomputable def goodFuns (x : ℕ → Circ) : Submodule ℂ C(Circ, ℂ) where
  carrier := {f | GoodFun x f}
  zero_mem' := by
    simp only [Set.mem_setOf_eq, GoodFun]
    simp
  add_mem' := by
    intro f g hf hg
    simp only [Set.mem_setOf_eq, GoodFun] at *
    have h1 : ∀ N : ℕ, ∫ t, (f + g) t ∂(emp x N)
        = (∫ t, f t ∂(emp x N)) + ∫ t, g t ∂(emp x N) := by
      intro N
      simpa using integral_add (integrable_continuousMap f (emp x N))
        (integrable_continuousMap g (emp x N))
    have h2 : ∫ t, (f + g) t ∂(volume : Measure Circ)
        = (∫ t, f t ∂(volume : Measure Circ)) + ∫ t, g t ∂(volume : Measure Circ) := by
      simpa using integral_add (integrable_continuousMap f volume)
        (integrable_continuousMap g volume)
    simp only [h1, h2]
    exact hf.add hg
  smul_mem' := by
    intro c f hf
    simp only [Set.mem_setOf_eq, GoodFun] at *
    have h1 : ∀ N : ℕ, ∫ t, (c • f) t ∂(emp x N) = c * ∫ t, f t ∂(emp x N) := by
      intro N
      simpa [smul_eq_mul] using integral_smul (μ := emp x N) c (fun t => f t)
    have h2 : ∫ t, (c • f) t ∂(volume : Measure Circ)
        = c * ∫ t, f t ∂(volume : Measure Circ) := by
      simpa [smul_eq_mul] using integral_smul (μ := (volume : Measure Circ)) c (fun t => f t)
    simp only [h1, h2]
    exact hf.const_mul c

