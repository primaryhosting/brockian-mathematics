import Mathlib

/-!
# Triangular Mod 5 Mem
Category: Cone Line
Target: Brockian.ConeLine.triangular_mod5_mem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.ConeLine

/-- The `n`-th triangular number, `T n = n (n+1) / 2` (natural-number division). -/
def T (n : ℕ) : ℕ := n * (n + 1) / 2

/-- Doubling the triangular number recovers `n (n+1)`. -/
lemma two_mul_T (n : ℕ) : 2 * T n = n * (n + 1) := by
  have h : 2 ∣ n * (n + 1) := (Nat.even_mul_succ_self n).two_dvd
  simp [T, Nat.mul_div_cancel' h]

/-- `T` has period `10` modulo `5`, in the strong sense that `T (10 q + r)` differs
from `T r` by a multiple of `5`. -/
lemma T_ten_mul_add (q r : ℕ) :
    T (10 * q + r) = 5 * (10 * q * q + 2 * q * r + q) + T r := by
  have h1 := two_mul_T (10 * q + r)
  have h2 := two_mul_T r
  nlinarith [h1, h2]

/-- Triangular numbers only occupy the residues `0`, `1`, `3` modulo `5`:
for every `n`, `(T n : ZMod 5) ∈ {0, 1, 3}`, so the rays `2` and `4` carry no
triangular number. -/
theorem triangular_mod5_mem (n : ℕ) : ((T n : ZMod 5)) ∈ ({0, 1, 3} : Set (ZMod 5)) := by
  have hn : n = 10 * (n / 10) + n % 10 := (Nat.div_add_mod n 10).symm
  have hr : n % 10 < 10 := Nat.mod_lt _ (by norm_num)
  have key : ((T n : ZMod 5)) = ((T (n % 10) : ZMod 5)) := by
    conv_lhs => rw [hn]
    rw [T_ten_mul_add]
    push_cast
    simp [show (5 : ZMod 5) = 0 by decide]
  rw [key]
  interval_cases h : (n % 10) <;> decide

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

