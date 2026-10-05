/-
# Gottesman Knill
Category: Frontier Qi
Target: QI.gottesman_knill
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Gottesman Knill
Category: Frontier Qi
Target: QI.gottesman_knill
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Matrix

namespace QI

/-! ## Bit vectors -/

/-- Computational basis labels for `n` qubits: bit strings of length `n`. -/
abbrev Bits (n : ℕ) := Fin n → Bool

variable {n : ℕ}

/-- Bitwise `xor` of two bit strings. -/

lemma sum_eq_pair (j : Fin n) (f : Bits n → ℂ) (b : Bits n)
    (h0 : ∀ c, ¬ agreeOff j c b → f c = 0) :
    ∑ c, f c = f (Function.update b j false) + f (Function.update b j true) := by
  classical
  have hne : (Function.update b j false : Bits n) ≠ Function.update b j true := by
    intro h; simpa using congrFun h j
  have key : ∀ c ∈ (Finset.univ : Finset (Bits n)),
      c ∉ ({Function.update b j false, Function.update b j true} : Finset (Bits n)) →
      f c = 0 := by
    intro c _ hc
    apply h0
    intro hagree
    have hcu : c = Function.update b j (c j) := by
      funext i
      by_cases hij : i = j
      · subst hij; simp
      · rw [Function.update_of_ne hij]
        exact hagree i hij
    apply hc
    cases hcj : c j
    · exact Finset.mem_insert.2 (Or.inl (hcu.trans (by rw [hcj])))
    · exact Finset.mem_insert.2 (Or.inr (by
        simp only [Finset.mem_singleton]
        exact hcu.trans (by rw [hcj])))
  rw [← Finset.sum_subset (Finset.subset_univ _) key, Finset.sum_pair hne]

