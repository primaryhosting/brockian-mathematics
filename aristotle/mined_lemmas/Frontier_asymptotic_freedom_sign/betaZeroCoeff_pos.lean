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

theorem betaZeroCoeff_pos {N nf : ℕ} (h : 2 * nf < 11 * N) :
    0 < betaZeroCoeff N nf := by
  have h' : (2 * nf : ℝ) < (11 * N : ℝ) := by exact_mod_cast h
  unfold betaZeroCoeff
  push_cast at h'
  linarith

/-- **Asymptotic freedom: the sign of the one-loop `SU(N)` beta function.**
For an `SU(N)` gauge theory with `nf` fermion flavours satisfying the asymptotic freedom
condition `2 nf < 11 N` (in particular for pure `SU(N)` Yang–Mills, `nf = 0`, `N ≥ 1`),
the one-loop beta function `β(g) = -b₀ g³/(16π²)` is strictly negative for every
positive coupling `g`. Hence the coupling decreases towards higher energies. -/
