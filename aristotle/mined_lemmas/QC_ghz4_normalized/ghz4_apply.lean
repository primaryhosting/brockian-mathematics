/-
# Ghz 4 Normalized
Category: Quantum Computing
Target: QC.ghz4_normalized
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace QC

/-- The state space of 4 qubits: the 16-dimensional complex Hilbert space whose
computational basis is indexed by bit strings `Fin 4 → Fin 2`. -/
abbrev Qubits4 : Type := EuclideanSpace ℂ (Fin 4 → Fin 2)

/-- The 4-qubit GHZ state `(|0000⟩ + |1111⟩)/√2`. -/

theorem ghz4_apply (x : Fin 4 → Fin 2) :
    ghz4.ofLp x =
      if x = (fun _ => 0) ∨ x = (fun _ => 1) then (1 / Real.sqrt 2 : ℝ) else 0 := by
  have hne : (fun _ => (0 : Fin 2)) ≠ (fun _ : Fin 4 => (1 : Fin 2)) := by
    intro h; have := congrFun h 0; simp at this
  by_cases h0 : x = (fun _ => 0)
  · subst h0; simp [ghz4, EuclideanSpace.single_apply, hne]
  · by_cases h1 : x = (fun _ => 1)
    · subst h1; simp [ghz4, EuclideanSpace.single_apply, Ne.symm hne]
    · simp [ghz4, EuclideanSpace.single_apply, h0, h1]

/-- The 4-qubit GHZ state `(|0000⟩ + |1111⟩)/√2` is a unit vector. -/
