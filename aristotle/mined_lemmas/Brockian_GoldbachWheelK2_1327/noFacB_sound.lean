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

theorem noFacB_sound :
    ∀ (k n m : Nat), noFacB n k = true → 2 ≤ m → m ≤ k → m * m ≤ n → ¬ m ∣ n := by
  intro k
  induction k with
  | zero => intro n m _ hm hmk _; omega
  | succ k ih =>
      intro n m h hm hmk hmn
      rw [noFacB, Bool.and_eq_true] at h
      obtain ⟨h1, h2⟩ := h
      rcases Nat.lt_or_ge m (k + 1) with hlt | hge
      · exact ih n m h2 hm (by omega) hmn
      · have hmeq : m = k + 1 := by omega
        subst hmeq
        rw [if_neg (by omega)] at h1
        rw [Nat.dvd_iff_mod_eq_zero]
        simpa using h1

/-- If no `m` with `2 ≤ m` and `m * m ≤ n` divides `n`, then `n` is prime. -/
