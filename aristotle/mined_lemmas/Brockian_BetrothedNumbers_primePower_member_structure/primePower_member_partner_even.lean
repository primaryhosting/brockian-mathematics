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
open scoped ArithmeticFunction.sigma
open ArithmeticFunction

namespace Brockian.BetrothedNumbers

/-- `IsBetrothedPair m n` says that `(m, n)` is a betrothed (quasi-amicable) pair:
two distinct positive integers each of whose sum of divisors equals `m + n + 1`,
equivalently, the sum of the nontrivial proper divisors of each equals the other. -/

lemma primePower_member_partner_even {p a n : ℕ} (hp : p.Prime) (hodd : Odd p)
    (h : IsBetrothedPair (p ^ a) n) : Even n := by
  obtain ⟨b, hab, hnb⟩ := primePower_partner hp h
  obtain ⟨hm, hn, hne, h1, h2⟩ := h
  have hcop := coprime_sigma_one_primePow hp b
  have hsig : σ 1 n = (p + 1) * σ 1 (σ 1 (p ^ b)) := by
    rw [hnb, sigma_one_prime_mul hp hcop]
  obtain ⟨c, hc⟩ : ∃ c, p + 1 = 2 * c := by
    obtain ⟨k, hk⟩ := hodd; exact ⟨k + 1, by omega⟩
  have hprod : (p + 1) * σ 1 (σ 1 (p ^ b)) = 2 * (c * σ 1 (σ 1 (p ^ b))) := by
    rw [hc]; ring
  have hpa : p ^ a % 2 = 1 := Nat.odd_iff.mp hodd.pow
  rw [Nat.even_iff]
  omega

/-- The exponent of a prime power member is odd. -/
