/-
# Square Mod 5 Mem
Category: Cone Line
Target: Brockian.ConeLine.square_mod5_mem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

namespace Brockian.ConeLine

/-- Perfect squares land only on rays `0`, `1`, `4` in `ZMod 5`. -/
theorem square_mod5_mem : ∀ n : ZMod 5, n ^ 2 = 0 ∨ n ^ 2 = 1 ∨ n ^ 2 = 4 := by
  decide

/-- The integer form: for every `n : ℤ`, the class of `n ^ 2` in `ZMod 5` is `0`, `1` or `4`. -/
theorem square_mod5_mem_int (n : ℤ) :
    ((n : ZMod 5)) ^ 2 = 0 ∨ ((n : ZMod 5)) ^ 2 = 1 ∨ ((n : ZMod 5)) ^ 2 = 4 :=
  square_mod5_mem (n : ZMod 5)

/-- The `Int.emod` form: `n ^ 2 % 5 ∈ ({0, 1, 4} : Set ℤ)` for every integer `n`. -/
theorem square_mod5_mem_emod (n : ℤ) : n ^ 2 % 5 = 0 ∨ n ^ 2 % 5 = 1 ∨ n ^ 2 % 5 = 4 := by
  have h : n % 5 = 0 ∨ n % 5 = 1 ∨ n % 5 = 2 ∨ n % 5 = 3 ∨ n % 5 = 4 := by omega
  have hsq : n ^ 2 % 5 = (n % 5) ^ 2 % 5 := by
    conv_lhs => rw [← Int.emod_emod_of_dvd n (dvd_refl 5)]
    rw [pow_two, pow_two, Int.mul_emod, Int.emod_emod_of_dvd n (dvd_refl 5)]
  rcases h with h | h | h | h | h <;> rw [hsq, h] <;> norm_num

end Brockian.ConeLine

