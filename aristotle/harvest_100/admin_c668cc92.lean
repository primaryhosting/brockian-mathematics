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

namespace Brockian.ConeLine

/-- The `n`-th triangular number, `T n = n(n+1)/2` (natural-number division). -/
def T (n : ℕ) : ℕ := n * (n + 1) / 2

/-- Twice a triangular number is `n(n+1)`. -/
lemma two_mul_T (n : ℕ) : 2 * T n = n * (n + 1) :=
  Nat.mul_div_cancel' (Nat.even_mul_succ_self n).two_dvd

/-- Decomposition of `T` along the period 10. -/
lemma T_ten_mul_add (q r : ℕ) : T (10 * q + r) = 50 * q * q + 5 * q * (2 * r + 1) + T r := by
  have h1 : 2 * T (10 * q + r) = (10 * q + r) * (10 * q + r + 1) := two_mul_T _
  have h2 : 2 * T r = r * (r + 1) := two_mul_T r
  have h3 : (10 * q + r) * (10 * q + r + 1)
      = 2 * (50 * q * q + 5 * q * (2 * r + 1)) + r * (r + 1) := by ring
  omega

/-- On the first period, the triangular residues are `0`, `1`, `3`. -/
lemma T_small_mem (r : ℕ) (hr : r < 10) :
    ((T r : ℕ) : ZMod 5) ∈ ({0, 1, 3} : Set (ZMod 5)) := by
  unfold T
  interval_cases r <;> norm_num <;> decide

/-- Triangular numbers only hit residues `0`, `1`, `3` modulo `5`. -/
theorem triangular_mod5_mem (n : ℕ) :
    ((n * (n + 1) / 2 : ℕ) : ZMod 5) ∈ ({0, 1, 3} : Set (ZMod 5)) := by
  have hn : n = 10 * (n / 10) + n % 10 := by omega
  have hr : n % 10 < 10 := Nat.mod_lt _ (by norm_num)
  have key : ((T n : ℕ) : ZMod 5) = ((T (n % 10) : ℕ) : ZMod 5) := by
    conv_lhs => rw [hn]
    rw [T_ten_mul_add]
    push_cast
    have h5 : (5 : ZMod 5) = 0 := by decide
    have h50 : (50 : ZMod 5) = 0 := by decide
    rw [h5, h50]
    ring
  have h : ((T n : ℕ) : ZMod 5) ∈ ({0, 1, 3} : Set (ZMod 5)) := by
    rw [key]; exact T_small_mem _ hr
  exact h

end Brockian.ConeLine

