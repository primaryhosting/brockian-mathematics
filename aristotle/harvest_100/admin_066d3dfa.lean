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

/-- The betrothed (quasi-amicable) partner map: `partner n = σ₁(n) - n - 1`,
the sum of the proper divisors of `n` other than `1`.  Natural subtraction is
harmless here: for `n ≥ 2` one has `σ₁(n) ≥ n + 1`. -/
def partner (n : ℕ) : ℕ := sigma 1 n - n - 1

/-- `m` and `n` form a betrothed (quasi-amicable) pair: both are positive,
distinct, and each is the sum of the nontrivial proper divisors of the other,
i.e. `σ₁(m) = σ₁(n) = m + n + 1`. -/
def IsBetrothedPair (m n : ℕ) : Prop :=
  0 < m ∧ 0 < n ∧ m ≠ n ∧ sigma 1 m = m + n + 1 ∧ sigma 1 n = m + n + 1

/-- `partner 0 = 0`, since `0` has no divisors. -/
@[simp] lemma partner_zero : partner 0 = 0 := by
  simp [partner]

/-- For positive `n`, `σ₁(n) - n - 1 = k` with `k > 0` is equivalent to
`σ₁(n) = n + k + 1`; this removes all truncated-subtraction issues. -/
lemma partner_eq_iff_of_pos {n k : ℕ} (hk : 0 < k) :
    partner n = k ↔ sigma 1 n = n + k + 1 := by
  unfold partner
  omega

/-- **Betrothed pairs are exactly the nontrivial 2-cycles of `partner`
supported on the positive integers.**

`(m, n)` is a betrothed pair iff `m > 0`, `partner m = n`, `partner n = m`
and `m ≠ n`.  (Positivity of `n` is automatic: `partner 0 = 0`, so a
`partner`-cycle through `0` cannot reach a positive number.) -/
theorem isBetrothedPair_iff_nontrivial_twoCycle (m n : ℕ) :
    IsBetrothedPair m n ↔ 0 < m ∧ partner m = n ∧ partner n = m ∧ m ≠ n := by
  constructor
  · rintro ⟨hm, hn, hmn, hsm, hsn⟩
    refine ⟨hm, ?_, ?_, hmn⟩
    · rw [partner_eq_iff_of_pos hn]; omega
    · rw [partner_eq_iff_of_pos hm]; omega
  · rintro ⟨hm, hpm, hpn, hmn⟩
    have hn : 0 < n := by
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · rw [partner_zero] at hpn; omega
      · exact hn
    rw [partner_eq_iff_of_pos hn] at hpm
    rw [partner_eq_iff_of_pos hm] at hpn
    exact ⟨hm, hn, hmn, by omega, by omega⟩

/-- The smallest betrothed pair: `(48, 75)`. -/
example : IsBetrothedPair 48 75 := by
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_⟩ <;>
    · rw [sigma_one_apply]; decide

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

