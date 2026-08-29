/-
# Shor Code Corrects
Category: Frontier Qi
Target: QI.shor_code_corrects
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Shor Code Corrects
Category: Frontier Qi
Target: QI.shor_code_corrects
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


open scoped BigOperators

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace QI

/-! ## Basic types

A computational basis state of one *block* of three qubits is a function `Fin 3 → Bool`;
a computational basis state of the nine qubits of the Shor code is a function
`Fin 3 → Blk`, i.e. three blocks of three qubits.  A qubit is addressed by a pair
`q : Q = Fin 3 × Fin 3` (block index, position inside the block). -/

/-- Computational basis states of one three-qubit block. -/
abbrev Blk := Fin 3 → Bool

/-- Computational basis states of the nine qubits. -/
abbrev Bas := Fin 3 → Blk

/-- Addresses of the nine qubits. -/
abbrev Q := Fin 3 × Fin 3

/-- Bitwise `xor` on a block. -/

lemma wt_le_two_of_supp (x z : Bas) (q q' : Q)
    (h : ∀ p : Q, p ≠ q → p ≠ q' → x p.1 p.2 = false ∧ z p.1 p.2 = false) :
    wt x z ≤ 2 := by
  rw [wt_eq_sum_Q]
  have hsub : ∑ p ∈ ({q, q'} : Finset Q), (if x p.1 p.2 || z p.1 p.2 then 1 else 0)
      = ∑ p : Q, (if x p.1 p.2 || z p.1 p.2 then 1 else 0) := by
    refine Finset.sum_subset (Finset.subset_univ _) ?_
    intro p _ hp
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hp
    obtain ⟨h1, h2⟩ := h p hp.1 hp.2
    simp [h1, h2]
  rw [← hsub]
  calc ∑ p ∈ ({q, q'} : Finset Q), (if x p.1 p.2 || z p.1 p.2 then 1 else 0)
      ≤ ∑ _p ∈ ({q, q'} : Finset Q), 1 := Finset.sum_le_sum fun p _ => by split <;> simp
    _ = ({q, q'} : Finset Q).card := by simp
    _ ≤ 2 := by simpa using Finset.card_insert_le q ({q'} : Finset Q)

