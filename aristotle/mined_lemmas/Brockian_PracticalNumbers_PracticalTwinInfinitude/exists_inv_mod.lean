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
# Practical Twin Infinitude
Category: Brockian Conjecture
Target: Brockian.PracticalNumbers.PracticalTwinInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Practical Twin Infinitude
Category: Brockian Conjecture
Target: Brockian.PracticalNumbers.PracticalTwinInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.PracticalNumbers

open Finset Pointwise

/-! ## Basic definitions -/

/-- The sum of the (positive) divisors of `n`. -/

theorem exists_inv_mod (A N : ℕ) (hN : 0 < N) (h : Nat.Coprime A N) :
    ∃ m, 1 ≤ m ∧ m ≤ N ∧ N ∣ A * m + 1 := by
  haveI : NeZero N := ⟨hN.ne'⟩
  set y : ZMod N := -((A : ZMod N)⁻¹) with hy
  set m₀ := y.val with hm₀
  have h1 : ((m₀ : ℕ) : ZMod N) = y := by rw [hm₀, ZMod.natCast_val, ZMod.cast_id]
  have hcast : ((if m₀ = 0 then N else m₀ : ℕ) : ZMod N) = y := by
    split
    · rename_i h0
      rw [ZMod.natCast_self, ← h1, h0]
      simp
    · exact h1
  refine ⟨if m₀ = 0 then N else m₀, ?_, ?_, ?_⟩
  · split <;> omega
  · split
    · exact le_rfl
    · exact (ZMod.val_lt y).le
  · rw [← ZMod.natCast_eq_zero_iff, Nat.cast_add, Nat.cast_mul, Nat.cast_one, hcast, hy,
      mul_neg, ZMod.coe_mul_inv_eq_one A h]
    ring

/-! ## Choosing matched exponents -/

