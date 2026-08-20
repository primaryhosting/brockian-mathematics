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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

/-- Sites of the `m × n` square lattice with periodic (toroidal) boundary conditions. -/
abbrev Site (m n : ℕ) : Type := ZMod m × ZMod n

/-- A spin configuration: a `± 1` value (encoded as a `Bool`) at every lattice site. -/
abbrev Config (m n : ℕ) : Type := Site m n → Bool

/-- The real spin value attached to a `Bool`. -/

noncomputable def partitionFunction (m n : ℕ) [NeZero m] [NeZero n] (K : ℝ) : ℝ :=
  ∑ σ : Config m n, Real.exp (K * bondSum σ)

/-- The (dimensionless) free energy per site, `(1 / N) log Z`. -/
