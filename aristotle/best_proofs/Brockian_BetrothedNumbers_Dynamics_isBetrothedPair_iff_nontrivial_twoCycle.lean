import Mathlib
/-!
# Is Betrothed Pair Iff Nontrivial Two Cycle
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.Dynamics.isBetrothedPair_iff_nontrivial_twoCycle
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped ArithmeticFunction.sigma

namespace Brockian.BetrothedNumbers.Dynamics

/-- The *betrothed partner map*: `partner n = σ₁ n - n - 1`, i.e. the sum of the
divisors of `n` that are strictly between `1` and `n` (subtraction is truncated). -/
def partner (n : ℕ) : ℕ := ArithmeticFunction.sigma 1 n - n - 1

/-- `(m, n)` is a *betrothed (quasi-amicable) pair*: two distinct positive integers with
`σ₁ m = σ₁ n = m + n + 1`. -/
def IsBetrothedPair (m n : ℕ) : Prop :=
  0 < m ∧ 0 < n ∧ m ≠ n ∧
    ArithmeticFunction.sigma 1 m = m + n + 1 ∧ ArithmeticFunction.sigma 1 n = m + n + 1

theorem partner_def (n : ℕ) : partner n = ArithmeticFunction.sigma 1 n - n - 1 := rfl

/-- Betrothed pairs are exactly the positive nontrivial `2`-cycles of the partner map
`partner n = σ₁ n - n - 1`. -/
theorem isBetrothedPair_iff_nontrivial_twoCycle (m n : ℕ) :
    IsBetrothedPair m n ↔
      0 < m ∧ 0 < n ∧ m ≠ n ∧ partner m = n ∧ partner n = m := by
  unfold IsBetrothedPair partner
  constructor
  · rintro ⟨hm, hn, hmn, hsm, hsn⟩
    exact ⟨hm, hn, hmn, by omega, by omega⟩
  · rintro ⟨hm, hn, hmn, hpm, hpn⟩
    exact ⟨hm, hn, hmn, by omega, by omega⟩

/-- Reformulation as a genuine `2`-cycle condition on a single number: `m` is a member of a
betrothed pair iff `m` is positive, `partner m` is positive, `partner (partner m) = m`, and
the cycle is nontrivial, i.e. `partner m ≠ m`. -/
theorem isBetrothedPair_partner_iff (m : ℕ) :
    IsBetrothedPair m (partner m) ↔
      0 < m ∧ 0 < partner m ∧ partner m ≠ m ∧ partner (partner m) = m := by
  rw [isBetrothedPair_iff_nontrivial_twoCycle]
  constructor
  · rintro ⟨hm, hn, hmn, _, hpn⟩
    exact ⟨hm, hn, fun h => hmn h.symm, hpn⟩
  · rintro ⟨hm, hn, hmn, hpn⟩
    exact ⟨hm, hn, fun h => hmn h.symm, rfl, hpn⟩

/-- The smallest betrothed pair `(48, 75)`. -/
example : IsBetrothedPair 48 75 := by
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_⟩ <;>
    simp [ArithmeticFunction.sigma_one_apply] <;> decide

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

