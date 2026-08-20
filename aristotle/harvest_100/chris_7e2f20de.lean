/-
# Ghz 7 Normalized
Category: Quantum Computing
Target: QC.ghz7_normalized
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace QC

/-- Computational basis states of 7 qubits, indexed by bit strings. -/
abbrev Qubits7 := Fin 7 → Bool

/-- The all-zeros bit string `|0000000⟩`. -/
def allZero : Qubits7 := fun _ => false

/-- The all-ones bit string `|1111111⟩`. -/
def allOne : Qubits7 := fun _ => true

/-- The amplitudes of the 7-qubit GHZ state: `1/√2` on `|0…0⟩` and on `|1…1⟩`,
zero elsewhere. -/
noncomputable def ghz7Amp (x : Qubits7) : ℂ :=
  if x = allZero then ((1 / Real.sqrt 2 : ℝ) : ℂ)
  else if x = allOne then ((1 / Real.sqrt 2 : ℝ) : ℂ) else 0

/-- The 7-qubit GHZ state `(|0…0⟩ + |1…1⟩)/√2` as a vector in the
Hilbert space `ℂ^(2^7)` whose basis is indexed by bit strings. -/
noncomputable def ghz7 : EuclideanSpace ℂ Qubits7 := WithLp.toLp 2 ghz7Amp

lemma allZero_ne_allOne : allZero ≠ allOne := by
  intro h
  have := congrFun h 0
  simp [allZero, allOne] at this

/-- The 7-qubit GHZ state is a unit vector. -/
theorem ghz7_normalized : ‖ghz7‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  have hpt : ∀ x : Qubits7, ‖ghz7.ofLp x‖ ^ 2 =
      (if x = allZero then (1/2 : ℝ) else 0) + (if x = allOne then (1/2 : ℝ) else 0) := by
    intro x
    by_cases h0 : x = allZero
    · subst h0
      simp [ghz7, ghz7Amp, allZero_ne_allOne]
    · by_cases h1 : x = allOne
      · subst h1
        simp [ghz7, ghz7Amp, h0]
      · simp [ghz7, ghz7Amp, h0, h1]
  rw [Finset.sum_congr rfl (fun x _ => hpt x), Finset.sum_add_distrib,
    Finset.sum_ite_eq' Finset.univ allZero (fun _ => (1/2 : ℝ)),
    Finset.sum_ite_eq' Finset.univ allOne (fun _ => (1/2 : ℝ))]
  norm_num

end QC

#print axioms QC.ghz7_normalized

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

