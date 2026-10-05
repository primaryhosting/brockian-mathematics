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

lemma noDivUpto_not_dvd :
    ∀ (b n k : ℕ), noDivUpto n b = true → 2 ≤ k → k ≤ b → k ≠ n → ¬ k ∣ n := by
  intro b
  induction b with
  | zero => intro n k _ hk hkb; omega
  | succ b ih =>
    match b with
    | 0 => intro n k _ hk hkb; omega
    | (b + 1) =>
      intro n k h hk hkb hkn
      rw [noDivUpto, Bool.and_eq_true] at h
      obtain ⟨h1, h2⟩ := h
      rcases Nat.lt_or_ge k (b + 2) with hlt | hge
      · exact ih n k h2 hk (by omega) hkn
      · have hkeq : k = b + 2 := by omega
        subst hkeq
        simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at h1
        rcases h1 with h1 | h1
        · exact fun hdvd => h1 (Nat.mod_eq_zero_of_dvd hdvd)
        · exact absurd h1.symm hkn

/-- Trial-division primality test, sound for inputs `< 1936 = 44 ^ 2`. -/
