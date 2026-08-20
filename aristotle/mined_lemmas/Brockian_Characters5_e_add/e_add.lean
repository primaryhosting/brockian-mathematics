/-
# E Add
Category: Characters
Target: Brockian.Characters5.e_add
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# E Add
Category: Characters
Target: Brockian.Characters5.e_add
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

namespace Brockian
namespace Characters5

/-- A primitive fifth root of unity in `ℂ`. -/

theorem e_add (j k : ZMod 5) : e (j + k) = e j * e k := by
  rw [e, e, e, ← pow_add]
  have hval : (j + k).val = (j.val + k.val) % 5 := by
    rw [ZMod.val_add]
  rw [hval]
  conv_rhs => rw [← Nat.div_add_mod (j.val + k.val) 5]
  rw [pow_add, pow_mul, omega_pow_five, one_pow, one_mul]

end Characters5
end Brockian

