/-
# Ghz 6 Normalized
Category: Quantum Computing
Target: QC.ghz6_normalized
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace QC

/-- The 6-qubit GHZ state `(|000000⟩ + |111111⟩)/√2`, as a vector in the complex
Euclidean space whose basis is indexed by the 6-bit strings `Fin 6 → Fin 2`:
the amplitude is `1/√2` on the all-zeros and all-ones strings, and `0` elsewhere. -/
noncomputable def ghz6 : EuclideanSpace ℂ (Fin 6 → Fin 2) :=
  WithLp.toLp 2 fun v =>
    if (v = fun _ => 0) ∨ (v = fun _ => 1) then ((1 / Real.sqrt 2 : ℝ) : ℂ) else 0

/-- The 6-qubit GHZ state is a unit vector. -/
theorem ghz6_normalized : ‖ghz6‖ = 1 := by
  have hz : ((fun _ => 0 : Fin 6 → Fin 2)) ≠ (fun _ => 1) := by
    intro h
    have := congrFun h 0
    simp at this
  rw [EuclideanSpace.norm_eq]
  have h : ∀ v : Fin 6 → Fin 2, ‖ghz6.ofLp v‖ ^ 2
      = (if v = (fun _ => 0) then (1 / 2 : ℝ) else 0)
        + (if v = (fun _ => 1) then (1 / 2 : ℝ) else 0) := by
    intro v
    simp only [ghz6, WithLp.ofLp_toLp]
    by_cases h0 : v = (fun _ => 0)
    · subst h0; simp [hz]
    · by_cases h1 : v = (fun _ => 1)
      · subst h1; simp [Ne.symm hz]
      · simp [h0, h1]
  simp only [h, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  norm_num

#print axioms QC.ghz6_normalized

end QC

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

