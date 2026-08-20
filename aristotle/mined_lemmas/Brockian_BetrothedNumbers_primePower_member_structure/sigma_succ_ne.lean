import Mathlib

/-!
# Prime Power Member Structure
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.primePower_member_structure
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Nat
open scoped Classical

set_option maxHeartbeats 1000000

namespace Brockian.BetrothedNumbers

open ArithmeticFunction Finset
open scoped ArithmeticFunction.sigma

/-- `IsBetrothedPair m n` : `m` and `n` form a betrothed (quasi-amicable) pair, i.e. the sum of
the nontrivial divisors (all divisors except `1` and the number itself) of each equals the other.
Equivalently `σ m = σ n = m + n + 1`.

The classical definition additionally requires `m ≠ n`; that hypothesis is not needed for any of
the results below, so it is omitted here (making the statements slightly stronger). -/

lemma sigma_succ_ne {p : ℕ} (hp : p.Prime) (hpodd : Odd p) (heq : σ 1 (p + 1) = 1 + p ^ 2) :
    False := by
  have hb : 2 * σ 1 (p + 1) ≤ (p + 1) * (p + 1 + 1) := two_mul_sigma_le
  rw [heq] at hb
  have hp3 : p ≤ 3 := by nlinarith
  have hp2 : 2 ≤ p := hp.two_le
  have : p = 3 := by
    rcases Nat.lt_or_ge p 3 with h | h
    · exfalso
      have : p = 2 := by omega
      rw [this] at hpodd
      exact (Nat.not_odd_iff_even.2 (by decide)) hpodd
    · omega
  subst this
  rw [show (3:ℕ) + 1 = 4 from rfl] at heq
  norm_num [show σ 1 4 = 7 from by decide] at heq

/-! ### Main theorem -/

/-- **Hagis–Lord, Proposition 4.** If a prime power `p ^ a` is a member of a betrothed
(quasi-amicable) pair with partner `n`, then `p` is odd, the exponent `a` is odd and larger
than `3`, and the partner `n` is even. -/
