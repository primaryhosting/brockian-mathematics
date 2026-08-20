import Mathlib

namespace Brockian.MsGaussSum

open Finset Complex

/-- The summand `exp (2πi k²/p)` is the value of the standard additive character at `k²`. -/

private lemma two_mul_eq_zero_iff (p : ℕ) [Fact p.Prime] (hp : Odd p) (m : ZMod p) :
    2 * m = 0 ↔ m = 0 := by
  have hp2 : p ≠ 2 := by rintro rfl; rcases hp with ⟨k, hk⟩; omega
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at h'
    exact hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out) Nat.prime_two).mp h')
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h' | h'
    · exact absurd h' h2
    · exact h'
  · rintro rfl; ring

/-- Orthogonality: the shifted character sums to `p` at `m = 0` and to `0` otherwise. -/
