/-
# No Communication
Category: Frontier Physics
Target: Frontier.no_communication
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (The header above is a plain block comment because Lean 4 requires every
-- `import` command to precede any module docstring; the identical header is
-- repeated as the module docstring immediately after the imports.)

import Mathlib

/-!
# No Communication
Category: Frontier Physics
Target: Frontier.no_communication
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped Kronecker
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

namespace Frontier

/-- The partial trace over the first ("Alice") tensor factor of a bipartite system
with Hilbert space `ℂ^ιA ⊗ ℂ^ιB`: states are matrices indexed by `ιA × ιB`, and
`ptraceLeft ρ` is the reduced state seen by Bob. -/

@[simp] lemma ptraceLeft_apply {ιA ιB : Type*} [Fintype ιA]
    (rho : Matrix (ιA × ιB) (ιA × ιB) ℂ) (b b' : ιB) :
    ptraceLeft rho b b' = ∑ a : ιA, rho (a, b) (a, b') := rfl

/-- Entrywise formula for conjugating a bipartite state by a local operator `K ⊗ 1`
acting on Alice's factor only. -/
