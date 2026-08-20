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
# Is Betrothed Pair Iff Nontrivial Two Cycle
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.Dynamics.isBetrothedPair_iff_nontrivial_twoCycle
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Brockian.BetrothedNumbers.Dynamics

open ArithmeticFunction

/-- The *quasi-aliquot* (betrothed partner) function:
`partner n = σ₁ n - n - 1`, i.e. the sum of the divisors of `n` other than `1` and `n`
(natural subtraction). -/
def partner (n : ℕ) : ℕ := sigma 1 n - n - 1

/-- A *betrothed* (quasi-amicable) pair: two distinct positive integers `m ≠ n`
with `σ₁ m = σ₁ n = m + n + 1`. -/
def IsBetrothedPair (m n : ℕ) : Prop :=
  0 < m ∧ 0 < n ∧ m ≠ n ∧ sigma 1 m = m + n + 1 ∧ sigma 1 n = m + n + 1

/-- A *nontrivial positive 2-cycle* of `partner`: `m` and `n` are positive and distinct,
and `partner` swaps them. -/
def IsNontrivialTwoCycle (m n : ℕ) : Prop :=
  0 < m ∧ 0 < n ∧ m ≠ n ∧ partner m = n ∧ partner n = m

/-- **Betrothed pairs are exactly the nontrivial positive 2-cycles of
`partner n = σ₁ n - n - 1`.** -/
theorem isBetrothedPair_iff_nontrivial_twoCycle (m n : ℕ) :
    IsBetrothedPair m n ↔ IsNontrivialTwoCycle m n := by
  unfold IsBetrothedPair IsNontrivialTwoCycle partner
  constructor
  · rintro ⟨hm, hn, hmn, hsm, hsn⟩
    refine ⟨hm, hn, hmn, ?_, ?_⟩ <;> omega
  · rintro ⟨hm, hn, hmn, hpm, hpn⟩
    refine ⟨hm, hn, hmn, ?_, ?_⟩ <;> omega

/-- Sanity check: `(48, 75)` is a betrothed pair, hence a nontrivial 2-cycle of `partner`. -/
example : IsBetrothedPair 48 75 := by
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_⟩ <;> decide

example : IsNontrivialTwoCycle 48 75 :=
  (isBetrothedPair_iff_nontrivial_twoCycle 48 75).mp
    ⟨by norm_num, by norm_num, by norm_num, by decide, by decide⟩

end Brockian.BetrothedNumbers.Dynamics

