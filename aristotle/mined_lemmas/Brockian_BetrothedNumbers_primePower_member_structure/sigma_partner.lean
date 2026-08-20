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

lemma sigma_partner {p c : ℕ} (hp : p.Prime) (hc : 0 < c) :
    σ 1 (p * ∑ i ∈ Finset.range c, p ^ i) = (p + 1) * σ 1 (∑ i ∈ Finset.range c, p ^ i) := by
  have hcop : Nat.Coprime p (∑ i ∈ Finset.range c, p ^ i) := by
    rw [Nat.Prime.coprime_iff_not_dvd hp]
    intro hdvd
    obtain ⟨c', rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
    rw [geom_sum_succ] at hdvd
    have : p ∣ 1 := (Nat.dvd_add_right (Dvd.intro _ rfl)).1 hdvd
    exact hp.one_lt.ne' (Nat.dvd_one.1 this)
  rw [isMultiplicative_sigma.map_mul_of_coprime hcop, sigma_prime hp]

/-! ### The base `2` case is impossible -/

