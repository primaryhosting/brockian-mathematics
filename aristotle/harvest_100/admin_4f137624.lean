import Mathlib

/-!
# Triangular Mod 5 Mem
Category: Cone Line
Target: Brockian.ConeLine.triangular_mod5_mem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

namespace Brockian.ConeLine

/-- The `n`-th triangular number, as a natural number (exact division by `2`). -/
def T (n : ℕ) : ℕ := n * (n + 1) / 2

lemma two_mul_T (n : ℕ) : 2 * T n = n * (n + 1) :=
  Nat.mul_div_cancel' (Nat.even_mul_succ_self n).two_dvd

/-- Shifting the index by `10` adds a multiple of `5` to the triangular number. -/
lemma T_add_ten (n : ℕ) : T (n + 10) = T n + (10 * n + 55) := by
  have h1 := two_mul_T n
  have h2 := two_mul_T (n + 10)
  nlinarith [h1, h2]

lemma T_mod_five (n : ℕ) : T n % 5 = 0 ∨ T n % 5 = 1 ∨ T n % 5 = 3 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases lt_or_ge n 10 with h | h
    · interval_cases n <;> decide
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 10 := ⟨n - 10, by omega⟩
      have hm := ih m (by omega)
      rw [T_add_ten]
      omega

/-- Triangular numbers land only on rays `0`, `1`, `3` modulo `5`. -/
theorem triangular_mod5_mem (n : ℕ) :
    ((n * (n + 1) / 2 : ℕ) : ZMod 5) ∈ ({0, 1, 3} : Set (ZMod 5)) := by
  have h : ((n * (n + 1) / 2 : ℕ) : ZMod 5) = ((T n % 5 : ℕ) : ZMod 5) := by
    rw [ZMod.natCast_mod]; rfl
  rcases T_mod_five n with h5 | h5 | h5 <;> rw [h, h5] <;> simp

end Brockian.ConeLine

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

