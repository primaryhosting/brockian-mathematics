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
# Data Processing
Category: Frontier Qi
Target: QI.data_processing
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Data Processing

Category: Frontier Qi.  Target: `QI.data_processing`.

(The header above is repeated as a plain comment at the top of the file, since Lean does not
allow a module docstring to precede the `import` commands.)

## Quantum relative entropy and the data-processing inequality

We work with finite-dimensional quantum systems, i.e. complex matrices indexed by a finite
type `n`, and we use the Umegaki relative entropy
`D(ρ‖σ) = Tr[ρ (log ρ - log σ)]`,
where the matrix logarithm is the one provided by the continuous functional calculus.
-/

namespace QI

open Matrix Unitary
open scoped ComplexOrder

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The matrix logarithm, defined through the continuous functional calculus. -/

lemma posDef_conj (u : unitary (Matrix n n ℂ)) (hρ : ρ.PosDef) :
    (star (u : Matrix n n ℂ) * ρ * (u : Matrix n n ℂ)).PosDef := by
  have hu : IsUnit (u : Matrix n n ℂ) := (Unitary.toUnits u).isUnit
  have := hρ.conjTranspose_mul_mul_same (B := (u : Matrix n n ℂ))
    (Matrix.mulVec_injective_of_isUnit hu)
  simpa [Matrix.star_eq_conjTranspose] using this

end Measurement

/-- **Data-processing inequality** for the quantum (Umegaki) relative entropy
`D(ρ‖σ) = Tr[ρ (log ρ - log σ)]`, for a von Neumann measurement channel `Φ = measurement u`
(measurement in the orthonormal basis given by the columns of the unitary `u`, recording the
outcome) and a reference state `σ` left invariant by the channel:

`D(Φ ρ ‖ Φ σ) ≤ D(ρ ‖ σ)`.

The two states are assumed to be positive definite (faithful states); note that the states are
not required to have unit trace, only the invariance `Φ σ = σ` of the reference state is used.
-/
