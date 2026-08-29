import Mathlib

/-!
# Shor Code Corrects
Category: Frontier Qi
Target: QI.shor_code_corrects
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open ComplexConjugate

namespace QI

/-! ## The 9-qubit Hilbert space -/

/-- Labels for the computational basis of 9 qubits. -/
abbrev Q := Fin 9 → Bool

/-- The state space of 9 qubits, `ℂ^(2^9)` with its standard Hermitian inner product. -/
abbrev H := EuclideanSpace ℂ Q

/-- Flip the `i`-th bit of a basis label. -/

lemma double_sum_delta (A B : T → ℂ) (c : Bool) :
    ∑ t : T, ∑ t' : T, A t * (B t' * (if c = true ∧ t = t' then (1:ℂ) else 0))
      = if c = true then ∑ t : T, A t * B t else 0 := by
  by_cases hc : c = true
  · simp [hc]
  · simp [hc]

