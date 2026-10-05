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

lemma primePower_member_exponent_odd {p a n : ℕ} (hp : p.Prime) (hodd : Odd p)
    (h : IsBetrothedPair (p ^ a) n) : Odd a := by
  obtain ⟨b, hab, hnb⟩ := primePower_partner hp h
  have hn : Even n := primePower_member_partner_even hp hodd h
  rw [hnb] at hn
  rcases Nat.even_mul.mp hn with h' | h'
  · exact absurd h' (Nat.not_even_iff_odd.mpr hodd)
  · have hpar := sigma_one_primePow_mod_two hp hodd b
    have := Nat.even_iff.mp h'
    rw [Nat.odd_iff]
    omega

/-- The exponent of a prime power member is not `3`. -/
