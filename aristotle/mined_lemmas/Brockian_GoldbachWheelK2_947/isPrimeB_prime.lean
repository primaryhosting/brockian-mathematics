/-
# Goldbach Wheel K 2 947
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_947
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Goldbach Wheel K 2 947
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_947
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

This file establishes a new member of the `GoldbachWheelK2` family: the binary
(`K = 2`) Goldbach property for the wheel modulus `947`, i.e. every even number
`n` with `4 ≤ n ≤ 2 * 947` is a sum of two primes `p + q` with `p ≤ q`.

The proof is a kernel-checked finite verification.  A trial-division primality
test `Brockian.isPrimeB`, sound for inputs below `44 ^ 2 = 1936`
(`Brockian.isPrimeB_prime`, via `Nat.prime_def_le_sqrt`), is combined with a
`decide`-checked search of a fixed wheel of small prime candidates.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace Brockian

/-- `noDivUpto n b = true` says that no `k` with `2 ≤ k ≤ b` and `k ≠ n` divides `n`. -/

lemma isPrimeB_prime {n : ℕ} (hn : n < 1936) (h : isPrimeB n = true) : Nat.Prime n := by
  rw [isPrimeB, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨h2, hd⟩ := h
  rw [Nat.prime_def_le_sqrt]
  refine ⟨h2, fun m hm hms => ?_⟩
  have hs : n.sqrt ≤ 43 := by
    have h44 : n.sqrt < 44 := Nat.sqrt_lt'.2 (by norm_num; omega)
    omega
  have hmn : m ≠ n := by
    have := Nat.sqrt_lt_self (show 1 < n by omega)
    omega
  exact noDivUpto_not_dvd 43 n m hd hm (le_trans hms hs) hmn

/-- The wheel of small prime candidates used as the smaller summand. -/
