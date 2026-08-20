/-
# Holevo Bound
Category: Frontier Qi
Target: QI.holevo_bound
Statement: Accessible information about a quantum ensemble is at most its Holevo χ quantity.
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Holevo Bound
Category: Frontier Qi
Target: QI.holevo_bound
Statement: Accessible information about a quantum ensemble is at most its Holevo χ quantity.
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

## Scope of the formalisation

The ensemble is a *commuting* (equivalently: simultaneously diagonalizable) family of states,
measured by a POVM that is diagonal in the same eigenbasis.  Concretely, a state `ρₓ` is recorded
by its spectrum `r x : Z → ℝ` in a fixed orthonormal eigenbasis indexed by `Z`, a POVM element
`E y` by its diagonal `Z → ℝ`, and the Born rule is `Pr[y | x] = ∑ z, r x z * E y z`.  In this
situation the von Neumann entropy is the Shannon entropy of the spectrum, so the Holevo quantity
`χ = S(∑ₓ pₓ ρₓ) - ∑ₓ pₓ S(ρₓ)` and the accessible information are the ones defined below, and
`QI.holevo_bound` is the Holevo inequality `I_acc ≤ χ` for such ensembles.  The bound is tight:
for a uniform ensemble of two orthogonal states, measured in their own basis, both sides equal
`log 2`.  The fully general (non-commuting) case is not covered here.
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

set_option grind.warning false

namespace QI

/-! ## The log-sum inequality -/

/-- **Log-sum inequality**: for nonnegative weights `a`, `b` on a finite set such that `b i = 0`
forces `a i = 0` (absolute continuity), one has
`(∑ a) * log ((∑ a) / (∑ b)) ≤ ∑ a i * log (a i / b i)`. -/

noncomputable def mutualInfo [Fintype X] [Fintype Y] (p : X → ℝ) (q : X → Y → ℝ) : ℝ :=
  ∑ x, ∑ y, p x * q x y * Real.log (q x y / ∑ x', p x' * q x' y)

/-- The accessible information of the ensemble `(p, r)` with measurement outcomes in `Y`:
the supremum, over all POVMs with outcome set `Y`, of the mutual information between the
label `X` and the measurement result. -/
