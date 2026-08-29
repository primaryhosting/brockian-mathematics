import Mathlib

/-!
# Onsager 2 D Ising
Category: Frontier Physics
Target: Frontier.onsager_2d_ising
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

namespace Frontier

/-- The real value of an Ising spin: `true ↦ +1`, `false ↦ -1`. -/

noncomputable def onsagerFree (β J : ℝ) : ℝ :=
  Real.log 2 + (1 / (2 * (2 * π) ^ 2)) * ∫ x in (0:ℝ)..(2 * π), ∫ y in (0:ℝ)..(2 * π),
    Real.log ((Real.cosh (2 * β * J)) ^ 2 - Real.sinh (2 * β * J) * (Real.cos x + Real.cos y))

/-- The partition function is a sum of exponentials, hence strictly positive. -/
