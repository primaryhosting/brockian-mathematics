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
# Ray Sum Eq Char Sum
Category: Characters
Target: Brockian.Characters5.raySum_eq_charSum
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Ray Sum Eq Char Sum
Category: Characters
Target: Brockian.Characters5.raySum_eq_charSum
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

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Brockian
namespace Characters5

/-- A primitive fifth root of unity. -/

theorem sum_e_eq_zero : ∑ b : ZMod 5, e b = 0 := by
  have h := isPrimitiveRoot_omega.geom_sum_eq_zero (by norm_num)
  rw [show (∑ b : ZMod 5, e b) = ∑ b : ZMod 5, omega ^ b.val from rfl, ← h]
  exact Finset.sum_nbij (fun b => b.val)
    (by simp [ZMod.val_lt])
    (fun a _ b _ hab => ZMod.val_injective _ hab)
    (fun k hk => by
      simp only [Finset.coe_range, Set.mem_Iio] at hk
      exact ⟨(k : ZMod 5), by simp, by simp [ZMod.val_natCast_of_lt hk]⟩)
    (fun _ _ => rfl)

/-- Orthogonality: the character sum detects whether `x = 0`. -/
