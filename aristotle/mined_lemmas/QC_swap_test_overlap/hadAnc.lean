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

/-
# Swap Test Overlap
Category: Quantum Computing
Target: QC.swap_test_overlap
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 requires `import` lines to precede any module docstring `/-! ... -/`,
-- so the header above is a plain block comment; it is repeated verbatim below.)

import Mathlib

/-!
# Swap Test Overlap
Category: Quantum Computing
Target: QC.swap_test_overlap
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QC

open scoped ComplexConjugate

variable {n : ℕ}

/-- A (pure) state of an `n`-level system, given by its amplitude vector. -/
abbrev State (n : ℕ) := Fin n → ℂ

/-- The amplitude vector of the tensor product `ψ ⊗ φ` of two states. -/

noncomputable def hadAnc (s : Fin 2 × (Fin n × Fin n) → ℂ) :
    Fin 2 × (Fin n × Fin n) → ℂ :=
  fun q => (s (0, q.2) + (if q.1 = 0 then 1 else -1) * s (1, q.2)) / (Real.sqrt 2 : ℝ)

/-- The controlled-SWAP (Fredkin) gate: it swaps the two `n`-level registers exactly
when the ancilla qubit is `1`. -/
