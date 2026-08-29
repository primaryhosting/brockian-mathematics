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

