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
# Landau Fourth Conjecture
Category: Brockian Conjecture
Target: Brockian.LandauNSquaredPlusOne.LandauFourthConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Landau Fourth Conjecture
Category: Brockian Conjecture
Target: Brockian.LandauNSquaredPlusOne.LandauFourthConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.LandauNSquaredPlusOne

open Zsqrtd

/-- A *Landau prime* is a prime natural number of the form `n ^ 2 + 1`. -/

theorem prime_dvd_sq_add_one_iff {p : ℕ} (hp : Nat.Prime p) :
    (∃ n : ℕ, p ∣ n ^ 2 + 1) ↔ (p = 2 ∨ p % 4 = 1) := by
  haveI : Fact p.Prime := ⟨hp⟩
  constructor
  · rintro ⟨n, hn⟩
    have h0 : ((n : ZMod p)) ^ 2 + 1 = 0 := by
      have h := (ZMod.natCast_eq_zero_iff (n ^ 2 + 1) p).2 hn
      push_cast at h
      exact h
    have hsq : IsSquare (-1 : ZMod p) := ⟨(n : ZMod p), by linear_combination -h0⟩
    have h3 : p % 4 ≠ 3 := (ZMod.exists_sq_eq_neg_one_iff (p := p)).1 hsq
    rcases hp.eq_two_or_odd with h | h
    · exact Or.inl h
    · exact Or.inr (by omega)
  · intro h
    have h3 : p % 4 ≠ 3 := by rcases h with rfl | h <;> omega
    obtain ⟨y, hy⟩ := (ZMod.exists_sq_eq_neg_one_iff (p := p)).2 h3
    refine ⟨y.val, (ZMod.natCast_eq_zero_iff _ p).1 ?_⟩
    push_cast [ZMod.natCast_val, ZMod.cast_id]
    rw [sq, ← hy]
    ring

/-- There are also infinitely many `n` for which `n ^ 2 + 1` is *not* prime. -/
