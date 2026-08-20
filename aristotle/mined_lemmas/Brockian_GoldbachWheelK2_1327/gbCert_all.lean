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

theorem gbCert_all : (List.range 664).all (fun k => k < 2 || gbCert (2 * k)) = true := by
  decide

/-- **Goldbach's conjecture on the `K = 2` wheel, verified up to `1327`.**
Every even natural number `n` with `4 ≤ n ≤ 1327` is a sum of two primes,
where primality is spelled out as `2 ≤ p ∧ ∀ m, m ∣ p → m = 1 ∨ m = p`. -/
