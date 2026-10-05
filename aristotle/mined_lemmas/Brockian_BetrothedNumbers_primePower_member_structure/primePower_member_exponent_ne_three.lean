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

lemma primePower_member_exponent_ne_three {p n : ℕ} (hp : p.Prime) (hodd : Odd p)
    (h : IsBetrothedPair (p ^ 3) n) : False := by
  obtain ⟨b, hab, hnb⟩ := primePower_partner hp h
  have hb : b = 1 := by omega
  subst hb
  rw [pow_one, sigma_one_prime hp] at hnb
  obtain ⟨hm, hn, hne, h1, h2⟩ := h
  have hcop : Nat.Coprime p (p + 1) := by simp
  have hsig : σ 1 n = (p + 1) * σ 1 (p + 1) := by rw [hnb, sigma_one_prime_mul hp hcop]
  have h3 : (p + 1) * σ 1 (p + 1) = (p + 1) * (p ^ 2 + 1) := by
    rw [← hsig, h2, hnb]; ring
  have hcancel : σ 1 (p + 1) = p ^ 2 + 1 := Nat.eq_of_mul_eq_mul_left (by omega) h3
  have hbound := two_mul_sigma_one_le (k := p + 1)
  rw [hcancel] at hbound
  have hple : p ≤ 3 := by nlinarith
  have hp2 : p ≠ 2 := by rintro rfl; exact (Nat.not_odd_iff_even.mpr (by decide)) hodd
  have hp3 : p = 3 := by have := hp.two_le; omega
  subst hp3
  revert hcancel
  decide

/-- **Hagis–Lord, Proposition 4.** If a prime power `p ^ a` is a member of a betrothed
(quasi-amicable) pair with partner `n`, then `p` is odd, `a` is odd with `a > 3`, and the
partner `n` is even. -/
