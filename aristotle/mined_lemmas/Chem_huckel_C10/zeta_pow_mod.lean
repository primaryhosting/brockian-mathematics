import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped Matrix

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

namespace Chem

attribute [local instance] Fin.instCommRing

/-! ### A primitive 10-th root of unity -/

/-- The primitive 10-th root of unity `exp (2πi/10)`. -/

lemma zeta_pow_mod (n : ℕ) : zeta ^ (n % 10) = zeta ^ n := by
  conv_rhs => rw [← Nat.div_add_mod n 10]
  rw [pow_add, pow_mul, zeta_pow_ten, one_pow, one_mul]

/-! ### The character `E` of `Fin 10` -/

/-- `E x = ζ ^ x`, a group homomorphism from `(Fin 10, +)` to `ℂˣ`. -/
