/-
# Is Betrothed Pair Iff Nontrivial Two Cycle
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.Dynamics.isBetrothedPair_iff_nontrivial_twoCycle
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Is Betrothed Pair Iff Nontrivial Two Cycle
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.Dynamics.isBetrothedPair_iff_nontrivial_twoCycle
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

Registered as: CLASSICAL_REFORMULATION.
-/

namespace Brockian.BetrothedNumbers.Dynamics

open ArithmeticFunction

/-- The *betrothed partner function*: `partner n = σ₁(n) - n - 1`, i.e. the sum of the
divisors of `n` other than `1` and `n` itself (natural subtraction, so it is `0` for
`n = 0, 1`). -/
def partner (n : ℕ) : ℕ := (sigma 1) n - n - 1

/-- A pair `(m, n)` of *betrothed* (quasi-amicable) numbers: two distinct positive
integers each of whose sum of proper divisors excluding `1` equals the other, i.e.
`σ₁(m) = σ₁(n) = m + n + 1`. -/
def IsBetrothedPair (m n : ℕ) : Prop :=
  0 < m ∧ 0 < n ∧ m ≠ n ∧ (sigma 1) m = m + n + 1 ∧ (sigma 1) n = m + n + 1

/-- `(m, n)` is a positive nontrivial `2`-cycle of `partner`. -/
def IsNontrivialTwoCycle (m n : ℕ) : Prop :=
  0 < m ∧ 0 < n ∧ m ≠ n ∧ partner m = n ∧ partner n = m

/-- If `n = partner m` is positive then the natural subtraction in `partner` does not
truncate, i.e. `σ₁(m) = m + n + 1`. -/
theorem sigma_eq_of_partner_eq {m n : ℕ} (h : partner m = n) (hn : 0 < n) :
    (sigma 1) m = m + n + 1 := by
  unfold partner at h
  omega

/-- **Characterization of betrothed pairs as nontrivial `2`-cycles of `partner`.**
A pair `(m, n)` is a betrothed (quasi-amicable) pair if and only if `m` and `n` are
distinct positive integers forming a `2`-cycle of `partner n = σ₁(n) - n - 1`. -/
theorem isBetrothedPair_iff_nontrivial_twoCycle (m n : ℕ) :
    IsBetrothedPair m n ↔ IsNontrivialTwoCycle m n := by
  constructor
  · rintro ⟨hm, hn, hmn, hsm, hsn⟩
    refine ⟨hm, hn, hmn, ?_, ?_⟩ <;> unfold partner <;> omega
  · rintro ⟨hm, hn, hmn, h1, h2⟩
    exact ⟨hm, hn, hmn, sigma_eq_of_partner_eq h1 hn, by
      have := sigma_eq_of_partner_eq h2 hm; omega⟩

/-- Sanity check: `(48, 75)` is a betrothed pair. -/
example : IsBetrothedPair 48 75 := by
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_⟩ <;> decide

end Brockian.BetrothedNumbers.Dynamics

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

