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

open Finset

/-- `sigmaOne n` is the sum of all positive divisors of `n`. -/

theorem BetrothedInfinitude :
    betrothedPairs.Infinite ↔ ∀ N : ℕ, ∃ m n : ℕ, N < m ∧ IsBetrothed m n := by
  constructor
  · intro hinf N
    by_contra hcon
    push_neg at hcon
    have hsub : Prod.fst '' betrothedPairs ⊆ Set.Iic N := by
      rintro x ⟨⟨m, n⟩, hp, rfl⟩
      by_contra hx
      exact hcon m n (lt_of_not_ge hx) hp
    exact (hinf.image injOn_fst_betrothedPairs) ((Set.finite_Iic N).subset hsub)
  · intro h hfin
    obtain ⟨N, hN⟩ := (hfin.image (Prod.fst)).bddAbove
    obtain ⟨m, n, hm, hb⟩ := h N
    have : m ≤ N := hN ⟨(m, n), hb, rfl⟩
    omega

end Brockian.BetrothedNumbers

