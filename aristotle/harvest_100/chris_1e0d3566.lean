/-
# Triangular Mod 5 Mem
Category: Cone Line
Target: Brockian.ConeLine.triangular_mod5_mem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- Note: Lean 4 requires `import` commands to precede every other command, including
-- module documentation `/-! ... -/`.  The requested header therefore appears above as an
-- ordinary block comment, and verbatim as the module docstring right after the import.

import Mathlib

/-!
# Triangular Mod 5 Mem
Category: Cone Line
Target: Brockian.ConeLine.triangular_mod5_mem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.ConeLine

/-- The `n`-th triangular number, computed in `ℕ` (division performed before casting). -/
def T (n : ℕ) : ℕ := n * (n + 1) / 2

lemma two_mul_T (n : ℕ) : 2 * T n = n * (n + 1) :=
  Nat.mul_div_cancel' (Nat.even_mul_succ_self n).two_dvd

/-- In `ZMod 5`, the triangular number `T n` equals `3 * n * (n + 1)`, since `2⁻¹ = 3`. -/
lemma T_cast_eq (n : ℕ) : (T n : ZMod 5) = 3 * (n : ZMod 5) * ((n : ZMod 5) + 1) := by
  have h : ((2 * T n : ℕ) : ZMod 5) = ((n * (n + 1) : ℕ) : ZMod 5) := by rw [two_mul_T]
  push_cast at h
  have h6 : (6 : ZMod 5) * (T n : ZMod 5) = 3 * ((n : ZMod 5) * ((n : ZMod 5) + 1)) := by
    rw [show (6 : ZMod 5) * (T n : ZMod 5) = 3 * (2 * (T n : ZMod 5)) by ring, h]
  rw [show (6 : ZMod 5) = 1 by decide, one_mul] at h6
  rw [h6]; ring

/-- Triangular numbers land only on the rays `0, 1, 3` modulo `5`;
rays `2` and `4` carry no triangular number. -/
theorem triangular_mod5_mem (n : ℕ) : (T n : ZMod 5) ∈ ({0, 1, 3} : Set (ZMod 5)) := by
  have key : ∀ x : ZMod 5, 3 * x * (x + 1) = 0 ∨ 3 * x * (x + 1) = 1 ∨ 3 * x * (x + 1) = 3 := by
    decide
  rcases key (n : ZMod 5) with h | h | h <;>
    simp [Set.mem_insert_iff, Set.mem_singleton_iff, T_cast_eq n, h]

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

