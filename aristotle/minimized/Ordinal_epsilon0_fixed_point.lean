/-
# Epsilon 0 Fixed Point
Category: Frontier Wave 2 (deeper machinery)
Target: Ordinal.epsilon0_fixed_point
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

namespace Ordinal

open scoped Ordinal

/-- `ε₀` is a fixed point of ordinal `ω`-exponentiation: `ω ^ ε₀ = ε₀`.

This is the `o = 0` instance of Mathlib's `Ordinal.omega0_opow_epsilon`, which states that every
value `ε_ o` of the epsilon function is a fixed point of `ω ^ ⬝`. -/

theorem epsilon0_fixed_point : (ω : Ordinal) ^ ε₀ = ε₀ :=
  omega0_opow_epsilon 0

/-- `ε₀` is the *least* fixed point of `ω ^ ⬝`: any ordinal `o` with `ω ^ o ≤ o` satisfies
`ε₀ ≤ o`. Together with `Ordinal.epsilon0_fixed_point` this characterizes `ε₀`. -/
