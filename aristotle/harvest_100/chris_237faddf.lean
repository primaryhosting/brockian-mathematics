/-!
# Square Mod 5 Mem
Category: Cone Line
Target: Brockian.ConeLine.square_mod5_mem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Brockian.ConeLine

/-- Perfect squares land only on rays `0`, `1`, `4` modulo `5`. -/
theorem square_mod5_mem : ∀ n : ZMod 5, n ^ 2 = 0 ∨ n ^ 2 = 1 ∨ n ^ 2 = 4 := by
  decide

/-- Integer form: for every `n : ℤ`, the residue of `n ^ 2` mod `5` is `0`, `1` or `4`. -/
theorem square_mod5_mem_int (n : ℤ) :
    ((n : ZMod 5) ^ 2 = 0 ∨ (n : ZMod 5) ^ 2 = 1 ∨ (n : ZMod 5) ^ 2 = 4) :=
  square_mod5_mem (n : ZMod 5)

/-- Integer form via `Int.emod`: `n ^ 2 % 5 ∈ ({0, 1, 4} : Set ℤ)`. -/
theorem square_emod5_mem (n : ℤ) : n ^ 2 % 5 = 0 ∨ n ^ 2 % 5 = 1 ∨ n ^ 2 % 5 = 4 := by
  have h : n % 5 = 0 ∨ n % 5 = 1 ∨ n % 5 = 2 ∨ n % 5 = 3 ∨ n % 5 = 4 := by omega
  have hsq : n ^ 2 % 5 = (n % 5) ^ 2 % 5 := by
    rw [Int.pow_emod]
  rcases h with h | h | h | h | h <;> rw [hsq, h] <;> norm_num

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

