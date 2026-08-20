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

namespace Chem

open Polynomial Matrix

/-- The primitive 17-th root of unity `exp (2πi/17)`. -/

lemma zeta_pow_congr {a b : ℕ} (h : a ≡ b [MOD 17]) : zeta ^ a = zeta ^ b := by
  rw [zeta_pow_mod a, zeta_pow_mod b, h]

/-- The eigenvalues predicted by Hückel theory for the cycle `C₁₇`. -/
