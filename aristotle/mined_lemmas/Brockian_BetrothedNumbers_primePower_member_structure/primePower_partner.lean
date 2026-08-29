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

lemma primePower_partner {p a n : ℕ} (hp : p.Prime) (h : IsBetrothedPair (p ^ a) n) :
    ∃ b : ℕ, a = b + 2 ∧ n = p * σ 1 (p ^ b) := by
  obtain ⟨hm, hn, hne, h1, h2⟩ := h
  match a with
  | 0 => simp at h1
  | 1 => rw [pow_one, sigma_one_prime hp] at h1; omega
  | (b + 2) =>
    refine ⟨b, rfl, ?_⟩
    rw [sigma_one_primePow_add_two hp b] at h1
    omega

/-- The prime of a prime power member of a betrothed pair is odd. -/
