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

theorem GoldbachWheelK2_1327 :
    ∀ n : ℕ, Even n → 4 ≤ n → n ≤ 2 * 1327 →
      ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p ≤ q ∧ p + q = n := by
  intro n hev h4 hub
  have hmem : n ∈ List.range' 4 1326 2 := by
    rw [List.mem_range']
    obtain ⟨k, hk⟩ := hev
    exact ⟨(n - 4) / 2, by omega, by omega⟩
  rw [← goldbachWitnesses_keys, List.mem_map] at hmem
  obtain ⟨x, hx, hxn⟩ := hmem
  have h := (List.all_eq_true.mp goldbachWitnesses_valid) x hx
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨h2, hle⟩, hub'⟩, hp⟩, hq⟩ := h
  subst hxn
  refine ⟨x.2, x.1 - x.2, prime_of_primeCert h2 (by omega) hp,
    prime_of_primeCert (by omega) (by omega) hq, by omega, by omega⟩

end Brockian

