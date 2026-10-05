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

/-!
# Is Betrothed Pair Iff Nontrivial Two Cycle
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.Dynamics.isBetrothedPair_iff_nontrivial_twoCycle
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.BetrothedNumbers.Dynamics

open ArithmeticFunction

/-- The *betrothed partner* map: `partner n = σ₁(n) - n - 1`, the sum of the
proper divisors of `n` other than `1`.  Subtraction is truncated subtraction on `ℕ`. -/
def partner (n : ℕ) : ℕ := sigma 1 n - n - 1

/-- A *betrothed* (quasi-amicable) pair: two distinct positive integers `m ≠ n`
with `σ₁(m) = σ₁(n) = m + n + 1`. -/
def IsBetrothedPair (m n : ℕ) : Prop :=
  0 < m ∧ 0 < n ∧ m ≠ n ∧ sigma 1 m = m + n + 1 ∧ sigma 1 n = m + n + 1

/-- If `partner m = n` with `n` positive, then `σ₁(m) = m + n + 1`
(this rules out the truncation of the natural subtraction). -/
lemma sigma_eq_of_partner_eq {m n : ℕ} (hn : 0 < n) (h : partner m = n) :
    sigma 1 m = m + n + 1 := by
  unfold partner at h
  omega

/-- The main characterization: a betrothed pair is exactly a nontrivial `2`-cycle of
`partner` consisting of positive integers. -/
theorem isBetrothedPair_iff_nontrivial_twoCycle (m n : ℕ) :
    IsBetrothedPair m n ↔
      0 < m ∧ 0 < n ∧ m ≠ n ∧ partner m = n ∧ partner n = m := by
  constructor
  · rintro ⟨hm, hn, hmn, hsm, hsn⟩
    refine ⟨hm, hn, hmn, ?_, ?_⟩ <;> unfold partner <;> omega
  · rintro ⟨hm, hn, hmn, hpm, hpn⟩
    refine ⟨hm, hn, hmn, sigma_eq_of_partner_eq hn hpm, ?_⟩
    have := sigma_eq_of_partner_eq hm hpn
    omega

/-- Sanity check: `(48, 75)` is a betrothed pair. -/
example : IsBetrothedPair 48 75 := by
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_⟩ <;>
    simp [sigma_one_apply] <;> decide

end Brockian.BetrothedNumbers.Dynamics

