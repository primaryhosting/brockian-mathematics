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

theorem goldbachCheck_spec {n : Nat} (h : goldbachCheck n = true) :
    ∃ p q : Nat, IsPrimeNat p ∧ IsPrimeNat q ∧ p ≤ 103 ∧ p + q = n := by
  rw [goldbachCheck, List.any_eq_true] at h
  obtain ⟨p, hp, hcheck⟩ := h
  rw [Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hcheck
  obtain ⟨⟨hpp, hqq⟩, hple⟩ := hcheck
  have hpw : p < 104 := by
    have := List.mem_range.1 (by simpa [wheel] using hp)
    omega
  exact ⟨p, n - p, isPrimeB_spec hpp, isPrimeB_spec hqq, by omega, by omega⟩

/-- The finite verification: every even `n` in `[4, 2654]` passes the wheel check. -/
