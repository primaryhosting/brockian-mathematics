import Mathlib

/-!
# Goldbach Wheel K 2 1327
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_1327
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- Note: Lean 4 requires all `import` commands to come before any other command,
-- including module docstrings, so `import Mathlib` precedes the header above.

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 40000

namespace Brockian

/-- A kernel-friendly primality certificate: `n` has no divisor `d` with
`2 ≤ d ≤ 52` and `d * d ≤ n`.  For `n < 53 ^ 2 = 2809` this is equivalent to
primality of `n` (given `2 ≤ n`). -/

theorem prime_of_primeCert {n : ℕ} (h2 : 2 ≤ n) (hlt : n < 2809)
    (hc : primeCert n = true) : Nat.Prime n := by
  rw [Nat.prime_def_le_sqrt]
  refine ⟨h2, fun m hm hms hdvd => ?_⟩
  have hmm : m * m ≤ n := Nat.le_sqrt.mp hms
  have hm52 : m ≤ 52 := by nlinarith
  have hmem : m ∈ List.range' 2 51 := by rw [List.mem_range'_1]; omega
  have h := (List.all_eq_true.mp hc) m hmem
  simp only [Bool.or_eq_true, decide_eq_true_eq, ne_eq] at h
  rcases h with h | h
  · omega
  · exact h (Nat.mod_eq_zero_of_dvd hdvd)

/-- For each even `n` with `4 ≤ n ≤ 2 * 1327`, a pair `(n, p)` where `p` is the least
prime such that `n - p` is also prime. -/
