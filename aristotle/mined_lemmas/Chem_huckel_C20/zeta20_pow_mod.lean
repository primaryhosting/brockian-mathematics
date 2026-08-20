/-
# Huckel C 20
Category: Chemistry
Target: Chem.huckel_C20
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Huckel C 20
Category: Chemistry
Target: Chem.huckel_C20
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

namespace Chem

open Polynomial Matrix

/-! ### The 20-th root of unity and the characters of `Fin 20` -/

/-- The primitive 20-th root of unity `exp (2πi/20)`. -/

lemma zeta20_pow_mod (x : ℕ) : zeta20 ^ (x % 20) = zeta20 ^ x := by
  conv_rhs => rw [← Nat.div_add_mod x 20]
  rw [pow_add, pow_mul, zeta20_pow_20, one_pow, one_mul]

/-- The additive character `m ↦ ζ^m` on `Fin 20`. -/
