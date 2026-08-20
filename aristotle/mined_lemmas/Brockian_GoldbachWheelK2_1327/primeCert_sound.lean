/-!
# Goldbach Wheel K 2 1327
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_1327
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
This file is deliberately import-free: Lean 4 does not allow a module docstring
(`/-! ... -/`) to precede the `import` commands, so the required header comment
forces the development to be self-contained in core Lean.  The primality
predicate is therefore spelled out explicitly (`2 ≤ p ∧ every divisor of p is 1
or p`).  The companion file `RequestProject.GoldbachWheelK2_1327Mathlib`
imports Mathlib and restates the result with `Nat.Prime`.
-/

namespace Brockian

/-- `noFacB n k = true` certifies that no `m` with `2 ≤ m ≤ k` and `m * m ≤ n` divides `n`.
Trial divisions are skipped as soon as `m * m > n`, which keeps kernel evaluation cheap. -/

theorem primeCert_sound {n : Nat} (hn : n ≤ 1680) (h : primeCert n = true) : IsPrimeNat n := by
  rw [primeCert, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨h2, hnf⟩ := h
  refine isPrimeNat_of_no_small_factor h2 (fun m hm hmm => ?_)
  have hm40 : m ≤ 40 := by
    rcases Nat.lt_or_ge m 41 with h' | h'
    · omega
    · have : 41 * 41 ≤ m * m := Nat.mul_le_mul h' h'
      omega
  exact noFacB_sound 40 n m hnf hm hm40 hmm

