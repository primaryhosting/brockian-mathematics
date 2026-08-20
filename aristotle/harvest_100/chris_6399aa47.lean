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
# Triangular Mod 5 Mem
Category: Cone Line
Target: Brockian.ConeLine.triangular_mod5_mem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Triangular Mod 5 Mem
Category: Cone Line
Target: Brockian.ConeLine.triangular_mod5_mem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.ConeLine

/-- The `n`-th triangular number. -/
def T (n : ℕ) : ℕ := n * (n + 1) / 2

/-- `n * (n + 1)` is twice the `n`-th triangular number. -/
lemma two_mul_T (n : ℕ) : 2 * T n = n * (n + 1) := by
  obtain ⟨m, hm⟩ := Nat.even_mul_succ_self n
  have hm' : n * (n + 1) = 2 * m := by omega
  simp [T, hm', Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]

/-- Triangular numbers decompose with period `10` modulo `5`. -/
lemma T_ten_mul_add (q r : ℕ) :
    T (10 * q + r) = 5 * (10 * q * q + 2 * q * r + q) + T r := by
  have h1 := two_mul_T (10 * q + r)
  have h2 := two_mul_T r
  have h3 : 2 * T (10 * q + r) = 2 * (5 * (10 * q * q + 2 * q * r + q) + T r) := by
    rw [h1, show 2 * (5 * (10 * q * q + 2 * q * r + q) + T r)
        = 10 * (10 * q * q + 2 * q * r + q) + 2 * T r from by ring, h2]
    ring
  omega

set_option maxHeartbeats 1000000 in
/-- Triangular numbers land only on rays `0`, `1`, `3` modulo `5`. -/
theorem triangular_mod5_mem (n : ℕ) :
    ((T n : ℕ) : ZMod 5) ∈ ({0, 1, 3} : Set (ZMod 5)) := by
  have hn : n = 10 * (n / 10) + n % 10 := by omega
  have hr : n % 10 < 10 := Nat.mod_lt _ (by norm_num)
  have key : ((T n : ℕ) : ZMod 5) = ((T (n % 10) : ℕ) : ZMod 5) := by
    conv_lhs => rw [hn, T_ten_mul_add]
    rw [Nat.cast_add, Nat.cast_mul, show ((5 : ℕ) : ZMod 5) = 0 from rfl,
      zero_mul, zero_add]
  rw [key]
  clear hn
  generalize hgen : n % 10 = r at hr ⊢
  interval_cases r <;> simp [T] <;> decide

end Brockian.ConeLine

