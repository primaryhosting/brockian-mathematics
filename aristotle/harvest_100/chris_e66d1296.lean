import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

/-
# FLT Statement
Category: Frontier — Prime Numbers
Target: Frontier.FLT_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Frontier

/-- The statement of Fermat's Last Theorem in explicit positive-integer form:
`x ^ n + y ^ n = z ^ n` has no solution in positive integers when `n > 2`. -/
def FLTClaim : Prop :=
  ∀ n x y z : ℕ, 2 < n → 0 < x → 0 < y → 0 < z → x ^ n + y ^ n ≠ z ^ n

/-- The explicit positive-integer form of FLT agrees with Mathlib's `FermatLastTheorem`. -/
theorem FLTClaim_iff_FermatLastTheorem : FLTClaim ↔ FermatLastTheorem := by
  constructor
  · intro h n hn a b c ha hb hc
    exact h n a b c (by omega) (Nat.pos_of_ne_zero ha) (Nat.pos_of_ne_zero hb)
      (Nat.pos_of_ne_zero hc)
  · intro h n x y z hn hx hy hz
    exact h n (by omega) x y z hx.ne' hy.ne' hz.ne'

/-- Every exponent `n ≥ 3` is divisible by `4` or by an odd prime. -/
theorem four_dvd_or_odd_prime_dvd {n : ℕ} (hn : 3 ≤ n) :
    4 ∣ n ∨ ∃ p : ℕ, p.Prime ∧ Odd p ∧ p ∣ n := by
  have odd_factor : ∀ m : ℕ, 2 ≤ m → ¬ 2 ∣ m → ∃ p : ℕ, p.Prime ∧ Odd p ∧ p ∣ m := by
    intro m hm hm2
    obtain ⟨p, hp, hpm⟩ := Nat.exists_prime_and_dvd (by omega : m ≠ 1)
    refine ⟨p, hp, ?_, hpm⟩
    rcases hp.eq_two_or_odd' with rfl | hodd
    · exact absurd hpm hm2
    · exact hodd
  by_cases h2 : 2 ∣ n
  · obtain ⟨m, rfl⟩ := h2
    by_cases hm2 : 2 ∣ m
    · obtain ⟨k, rfl⟩ := hm2
      exact Or.inl ⟨k, by ring⟩
    · obtain ⟨p, hp, hodd, hpm⟩ := odd_factor m (by omega) hm2
      exact Or.inr ⟨p, hp, hodd, hpm.mul_left 2⟩
  · obtain ⟨p, hp, hodd, hpn⟩ := odd_factor n (by omega) h2
    exact Or.inr ⟨p, hp, hodd, hpn⟩

/-- Base case: FLT for the exponent `4` (Mathlib's `fermatLastTheoremFour`). -/
theorem FLT_four : FermatLastTheoremFor 4 := fermatLastTheoremFour

/-- Base case: FLT for the exponent `3` (Mathlib's `fermatLastTheoremThree`). -/
theorem FLT_three : FermatLastTheoremFor 3 := fermatLastTheoremThree

/-- **Fermat's Last Theorem, reduced to odd prime exponents.**

`x ^ n + y ^ n = z ^ n` has no solution in positive integers for `n > 2` if and only if it has
no such solution for every odd prime exponent `p`.

The nontrivial direction uses the classical reduction: every `n ≥ 3` is divisible by `4` or by
an odd prime, the case of exponent `4` being Fermat's own descent argument, available in Mathlib
as `fermatLastTheoremFour`; divisibility of exponents transfers the statement via
`FermatLastTheoremFor.mono`. -/
theorem FLT_statement :
    FLTClaim ↔ ∀ p : ℕ, p.Prime → Odd p → FermatLastTheoremFor p := by
  rw [FLTClaim_iff_FermatLastTheorem]
  constructor
  · intro h p hp hodd
    have hp2 : p ≠ 2 := by rintro rfl; exact absurd hodd (by decide)
    have hp2' := hp.two_le
    exact h p (by omega)
  · intro h n hn
    rcases four_dvd_or_odd_prime_dvd hn with h4 | ⟨p, hp, hodd, hpn⟩
    · exact FermatLastTheoremFor.mono h4 fermatLastTheoremFour
    · exact FermatLastTheoremFor.mono hpn (h p hp hodd)

end Frontier

