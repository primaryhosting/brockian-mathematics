/-
# Ghz 5 Normalized
Category: Quantum Computing
Target: QC.ghz5_normalized
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace QC

/-- The computational basis label `|00000⟩` of a 5-qubit register. -/
def allZero : Fin 5 → Bool := fun _ => false

/-- The computational basis label `|11111⟩` of a 5-qubit register. -/
def allOne : Fin 5 → Bool := fun _ => true

lemma allZero_ne_allOne : allZero ≠ allOne := by
  intro h
  have := congrFun h 0
  simp [allZero, allOne] at this

/-- The 5-qubit GHZ state `(|00000⟩ + |11111⟩)/√2`, as a vector in the
Hilbert space `ℂ^(2^5)` whose coordinates are indexed by bit strings of length 5. -/
noncomputable def ghz5 : EuclideanSpace ℂ (Fin 5 → Bool) :=
  WithLp.toLp 2 (fun i =>
    if i = allZero then ((1 / Real.sqrt 2 : ℝ) : ℂ)
    else if i = allOne then ((1 / Real.sqrt 2 : ℝ) : ℂ)
    else 0)

lemma norm_sq_coord (i : Fin 5 → Bool) :
    ‖ghz5.ofLp i‖ ^ 2 = (if i = allZero then (1 : ℝ) / 2 else 0)
      + (if i = allOne then (1 : ℝ) / 2 else 0) := by
  by_cases h0 : i = allZero
  · simp [ghz5, h0, allZero_ne_allOne]
  · by_cases h1 : i = allOne
    · simp [ghz5, h1, allZero_ne_allOne.symm]
    · simp [ghz5, h0, h1]

/-- The 5-qubit GHZ state is a unit vector. -/
theorem ghz5_normalized : ‖ghz5‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  have hsum : ∑ i : Fin 5 → Bool, ‖ghz5.ofLp i‖ ^ 2 = 1 := by
    simp only [norm_sq_coord]
    rw [Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ allZero (fun _ => (1 : ℝ) / 2),
      Finset.sum_ite_eq' Finset.univ allOne (fun _ => (1 : ℝ) / 2)]
    norm_num
  rw [hsum, Real.sqrt_one]

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

