/-
# Ehrenfest
Category: Quantum Physics
Target: QPhys.ehrenfest
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace QPhys

open ComplexConjugate Finset

variable {n : ℕ}

/-- The expectation value `⟨A⟩ = ⟪ψ, A ψ⟫` of an observable `A` (given as a matrix)
in the state `ψ` (a vector of `ℂ^n`). -/

private lemma sum3_swap13 (F : Fin n → Fin n → Fin n → ℂ) :
    ∑ i, ∑ j, ∑ k, F i j k = ∑ k, ∑ j, ∑ i, F i j k := by
  calc ∑ i, ∑ j, ∑ k, F i j k = ∑ j, ∑ i, ∑ k, F i j k := Finset.sum_comm
    _ = ∑ j, ∑ k, ∑ i, F i j k := Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ k, ∑ j, ∑ i, F i j k := Finset.sum_comm

/-- Product rule for the expectation value of a time-dependent observable in a
time-dependent state. -/
