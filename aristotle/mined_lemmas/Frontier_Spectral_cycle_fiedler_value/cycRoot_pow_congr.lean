import Mathlib
/-!
# Cycle Fiedler Value
Category: Frontier — Spectral Geometry
Target: Frontier.Spectral.cycle_fiedler_value
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier.Spectral

open Finset Matrix SimpleGraph

/-- The angle `2π/n` for the cycle `C_n` with `n = m + 3`. -/

lemma cycRoot_pow_congr {a b : ℕ} (h : a ≡ b [MOD m + 3]) :
    cycRoot m ^ a = cycRoot m ^ b := by
  have hp : cycRoot m ^ (m + 3) = 1 := cycRoot_isPrimitiveRoot.pow_eq_one
  have key : ∀ c : ℕ, cycRoot m ^ c = cycRoot m ^ (c % (m + 3)) := by
    intro c
    conv_lhs => rw [← Nat.mod_add_div c (m + 3)]
    rw [pow_add, pow_mul, hp, one_pow, mul_one]
  rw [key a, key b, h]

