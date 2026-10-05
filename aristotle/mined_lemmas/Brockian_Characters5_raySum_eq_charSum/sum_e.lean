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
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Brockian
namespace Characters5

/-- A primitive fifth root of unity. -/
noncomputable def ω : ℂ := Complex.exp (2 * Real.pi * Complex.I / 5)

/-- The standard additive character of `ZMod 5` valued in `ℂ`. -/

theorem sum_e : ∑ a : ZMod 5, e a = 0 := by
  have h := isPrimitiveRoot_ω.geom_sum_eq_zero (by norm_num)
  rw [← h]
  exact Fin.sum_univ_eq_sum_range (fun i => ω ^ i) 5

/-- Orthogonality: the character sum over `ZMod 5` detects `x = 0`. -/
