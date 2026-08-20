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

theorem gbCert_sound {n : Nat} (hn : n ≤ 1680) (h : gbCert n = true) :
    ∃ p q : Nat, IsPrimeNat p ∧ IsPrimeNat q ∧ p + q = n := by
  rw [gbCert, List.any_eq_true] at h
  obtain ⟨p, hp, hpc⟩ := h
  rw [List.mem_range] at hp
  rw [Bool.and_eq_true] at hpc
  exact ⟨p, n - p, primeCert_sound (by omega) hpc.1,
    primeCert_sound (by omega) hpc.2, by omega⟩

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000 in
/-- The kernel-checked verification of the Goldbach property for every even
number `2 * k` with `2 ≤ k < 664`, i.e. for every even `n` with `4 ≤ n ≤ 1326`. -/
