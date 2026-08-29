import Mathlib

/-!
# Abc Statement
Category: Frontier — Prime Numbers
Target: Frontier.abc_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators

namespace Frontier

/-- The radical of a natural number: the product of its distinct prime factors. -/

lemma rad_mul_le {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) : rad (a * b) ≤ rad a * rad b := by
  classical
  have h : rad (a * b) * (∏ p ∈ a.primeFactors ∩ b.primeFactors, p) = rad a * rad b := by
    unfold rad
    rw [Nat.primeFactors_mul ha hb]
    exact Finset.prod_union_inter
  have hpos : 0 < ∏ p ∈ a.primeFactors ∩ b.primeFactors, p :=
    Finset.prod_pos fun p hp =>
      (Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_inter_left hp)).pos
  calc rad (a * b) ≤ rad (a * b) * (∏ p ∈ a.primeFactors ∩ b.primeFactors, p) :=
        Nat.le_mul_of_pos_right _ hpos
    _ = rad a * rad b := h

