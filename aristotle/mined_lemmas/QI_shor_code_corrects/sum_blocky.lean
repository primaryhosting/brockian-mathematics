/-
# Shor Code Corrects
Category: Frontier Qi
Target: QI.shor_code_corrects
Statement: The 9-qubit Shor code corrects an arbitrary single-qubit error.
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Shor Code Corrects
Category: Frontier Qi
Target: QI.shor_code_corrects
Statement: The 9-qubit Shor code corrects an arbitrary single-qubit error.
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators

namespace QI

/-- Index set of the nine qubits: three blocks of three. -/
abbrev Idx : Type := Fin 3 × Fin 3

/-- Computational basis states of the nine qubits are bit strings. -/
abbrev Bits : Type := Idx → Bool

/-- Pointwise `xor` of two bit strings. -/

lemma sum_blocky (F : Bits → ℤ) (h : ∀ c, ¬ Blocky c → F c = 0) :
    ∑ c : Bits, F c = ∑ t : Fin 3 → Bool, F (expand t) := by
  have h1 : ∑ c ∈ Finset.univ.filter Blocky, F c = ∑ c : Bits, F c := by
    refine Finset.sum_subset (Finset.filter_subset _ _) ?_
    intro c _ hc
    exact h c (by simpa using hc)
  rw [← h1, filter_blocky, Finset.sum_image (fun t _ t' _ htt' => expand_injective htt')]

/-! ## Block parities -/

/-- Parity of the restriction of `u` to block `m`. -/
