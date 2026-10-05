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

namespace Brockian.BetrothedNumbers

/-- The *betrothed partner* map: `partner n = σ₁(n) - n - 1`, i.e. the sum of the
proper divisors of `n` excluding `1` (natural subtraction). -/
def partner (n : ℕ) : ℕ := ArithmeticFunction.sigma 1 n - n - 1

/-- `m` and `n` form a *betrothed* (quasi-amicable) pair: they are distinct positive
integers with `σ₁(m) = σ₁(n) = m + n + 1`. -/
def IsBetrothedPair (m n : ℕ) : Prop :=
  0 < m ∧ 0 < n ∧ m ≠ n ∧
    ArithmeticFunction.sigma 1 m = m + n + 1 ∧ ArithmeticFunction.sigma 1 n = m + n + 1

namespace Dynamics

/-- Key arithmetic step: for a positive value of `partner`, natural subtraction can be
inverted, i.e. `partner m = n` with `0 < n` is equivalent to `σ₁(m) = m + n + 1`. -/
theorem partner_eq_iff_sigma_eq {m n : ℕ} (hn : 0 < n) :
    partner m = n ↔ ArithmeticFunction.sigma 1 m = m + n + 1 := by
  unfold partner
  omega

/-- **Betrothed pairs are exactly the positive nontrivial 2-cycles of `partner`.**

A pair `(m, n)` is betrothed iff both entries are positive, they are distinct
(nontriviality: the 2-cycle is not a fixed point), and `partner` swaps them. -/
theorem isBetrothedPair_iff_nontrivial_twoCycle (m n : ℕ) :
    IsBetrothedPair m n ↔ 0 < m ∧ 0 < n ∧ m ≠ n ∧ partner m = n ∧ partner n = m := by
  constructor
  · rintro ⟨hm, hn, hmn, hsm, hsn⟩
    refine ⟨hm, hn, hmn, ?_, ?_⟩
    · rw [partner_eq_iff_sigma_eq hn]; exact hsm
    · rw [partner_eq_iff_sigma_eq hm]; omega
  · rintro ⟨hm, hn, hmn, hpm, hpn⟩
    rw [partner_eq_iff_sigma_eq hn] at hpm
    rw [partner_eq_iff_sigma_eq hm] at hpn
    exact ⟨hm, hn, hmn, hpm, by omega⟩

/-- Equivalent "orbit" phrasing: a betrothed pair is a genuine 2-cycle, i.e.
`partner (partner m) = m` with `partner m ≠ m`, both entries positive. -/
theorem isBetrothedPair_iff_twoCycle_of_partner (m : ℕ) (n : ℕ) (hnm : n = partner m) :
    IsBetrothedPair m n ↔ 0 < m ∧ 0 < partner m ∧ partner m ≠ m ∧ partner (partner m) = m := by
  subst hnm
  rw [isBetrothedPair_iff_nontrivial_twoCycle]
  constructor
  · rintro ⟨hm, hp, hne, -, h⟩
    exact ⟨hm, hp, fun h' => hne h'.symm, h⟩
  · rintro ⟨hm, hp, hne, h⟩
    exact ⟨hm, hp, fun h' => hne h'.symm, rfl, h⟩

/-- The smallest betrothed pair `(48, 75)`. -/
example : IsBetrothedPair 48 75 := by
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_⟩ <;> decide

end Dynamics

end Brockian.BetrothedNumbers

