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
# Betrothed Infinitude
Category: Brockian Conjecture
Target: Brockian.BetrothedNumbers.BetrothedInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Betrothed Infinitude
Category: Brockian Conjecture
Target: Brockian.BetrothedNumbers.BetrothedInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.BetrothedNumbers

/-- The sum-of-divisors function `σ₁ n = ∑_{d ∣ n} d` (with the convention `σ₁ 0 = 0`). -/

theorem BetrothedInfinitude :
    (∀ N : ℕ, ∃ p : ℕ × ℕ, N < p.1 ∧ Betrothed p.1 p.2) ↔ betrothedPairs.Infinite := by
  constructor
  · intro h hfin
    obtain ⟨N, hN⟩ := (hfin.image Prod.fst).bddAbove
    obtain ⟨p, hp, hpB⟩ := h N
    have : p.1 ≤ N := hN ⟨p, hpB, rfl⟩
    omega
  · intro hinf N
    by_contra hcon
    push_neg at hcon
    refine hinf (Set.Finite.of_finite_image ?_ injOn_fst_betrothedPairs)
    refine Set.Finite.subset (Set.finite_Iic N) ?_
    rintro _ ⟨p, hp, rfl⟩
    exact le_of_not_gt fun hgt => hcon p hgt hp

/-- The set of *betrothed numbers*: numbers that belong to some betrothed pair. -/
