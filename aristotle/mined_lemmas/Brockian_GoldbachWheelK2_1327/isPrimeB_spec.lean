/-!
# Goldbach Wheel K 2 1327
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_1327
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- This module is deliberately import-free (Lean forbids `import` after the header
-- comment above), so primality is spelled out from first principles here.  The
-- companion module `RequestProject.GoldbachWheelK2_1327Mathlib` proves that
-- `Brockian.IsPrimeNat` coincides with Mathlib's `Nat.Prime`, and restates the
-- main theorem in Mathlib's vocabulary.

namespace Brockian

set_option maxRecDepth 100000

/-- Primality, from first principles: `n` is at least `2` and its only divisors are
`1` and `n`. -/

theorem isPrimeB_spec {n : Nat} (h : isPrimeB n = true) : IsPrimeNat n := by
  rw [isPrimeB, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨h2, hT⟩ := h
  refine ⟨h2, ?_⟩
  intro m hm
  by_cases hm1 : m = 1
  · exact Or.inl hm1
  by_cases hmn : m = n
  · exact Or.inr hmn
  exfalso
  obtain ⟨k, hk⟩ := hm
  have hm0 : m ≠ 0 := by rintro rfl; omega
  have hk0 : k ≠ 0 := by rintro rfl; omega
  have hm2 : 2 ≤ m := by omega
  have hk1 : k ≠ 1 := by rintro rfl; omega
  have hk2 : 2 ≤ k := by omega
  rcases Nat.le_total (m * m) n with hmm | hmm
  · exact no_small_divisor hT m hm2 hmm ⟨k, hk⟩
  · have hkk : k * k ≤ n := by
      have hkm : k ≤ m :=
        Nat.le_of_mul_le_mul_left (by rw [← hk]; exact hmm) (by omega)
      calc k * k ≤ m * k := Nat.mul_le_mul_right k hkm
        _ = n := by omega
    exact no_small_divisor hT k hk2 hkk ⟨m, by rw [hk, Nat.mul_comm]⟩

/-- The wheel of candidate small summands. -/
