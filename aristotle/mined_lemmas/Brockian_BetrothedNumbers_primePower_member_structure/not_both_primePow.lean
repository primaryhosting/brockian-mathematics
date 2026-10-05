/-
# Prime Power Member Structure
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.primePower_member_structure
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Prime Power Member Structure
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.primePower_member_structure
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped ArithmeticFunction.sigma

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Brockian.BetrothedNumbers

open Finset ArithmeticFunction

/-- `IsBetrothedPair m n` says that `(m, n)` is a betrothed (quasi-amicable) pair:
two distinct positive integers each of whose sum of divisors equals `m + n + 1`;
equivalently, the sum of the proper divisors of each member is the other member plus one. -/

theorem not_both_primePow {p a q b : ℕ} (hp : p.Prime) (hq : q.Prime)
    (h : IsBetrothedPair (p ^ a) (q ^ b)) : False := by
  obtain ⟨-, -, -, heven⟩ := primePower_member_structure hp h
  obtain ⟨hqodd, -, -, -⟩ := primePower_member_structure hq h.symm
  have hdvd : (2 : ℕ) ∣ q ^ b := heven.two_dvd
  have hq2 : q = 2 :=
    ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hq).mp
      (Nat.Prime.dvd_of_dvd_pow Nat.prime_two hdvd)).symm
  rw [hq2] at hqodd
  simp [Nat.odd_iff] at hqodd

end Brockian.BetrothedNumbers

