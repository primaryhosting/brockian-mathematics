/-
# Asymptotic Freedom Sign
Category: Frontier Physics
Target: Frontier.asymptotic_freedom_sign
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` to precede any module docstring `/-! ... -/`, so the header
-- above is written as a plain block comment; it is repeated as a module docstring below.)

import Mathlib

/-!
# Asymptotic Freedom Sign
Category: Frontier Physics
Target: Frontier.asymptotic_freedom_sign
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

/-- The one-loop beta-function coefficient `b₀` for an `SU(N)` gauge theory with
`nf` Dirac fermions in the fundamental representation:
`b₀ = 11N/3 - 2 nf/3`. -/

noncomputable def betaZeroCoeff (N nf : ℕ) : ℝ :=
  11 * (N : ℝ) / 3 - 2 * (nf : ℝ) / 3

/-- The one-loop beta function of the gauge coupling `g` for `SU(N)` with `nf` flavours:
`β(g) = - b₀ g³ / (16 π²)`. -/
