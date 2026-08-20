/-!
# Admissibility Ktuple K 4
Category: Brockian Corpus
Target: Brockian.AdmissibilityKTupleK4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian

/-- Primality of a natural number, stated from first principles:
`p` is at least `2` and its only divisors are `1` and `p`. -/

theorem missed_residue_large (q : Nat) (hq : 9 ≤ q) :
    ∃ a < q, ∀ h ∈ [0, 2, 6, 8], h % q ≠ a := by
  refine ⟨1, by omega, ?_⟩
  intro h hh
  have hlt : h < q := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
    rcases hh with rfl | rfl | rfl | rfl <;> omega
  rw [Nat.mod_eq_of_lt hlt]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl <;> omega

/-- **Admissibility for `4`-tuples**: the prime `4`-tuple pattern `(0, 2, 6, 8)` is
admissible, i.e. for every prime `p` some residue class modulo `p` is avoided by all of
`0, 2, 6, 8`. -/
