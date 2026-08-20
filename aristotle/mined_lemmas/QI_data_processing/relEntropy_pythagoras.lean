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

theorem relEntropy_pythagoras (hd : σ.IsDiag) :
    relEntropy ρ σ = relEntropy ρ (dephase ρ) + relEntropy (dephase ρ) σ := by
  have h1 : (ρ * logm (dephase ρ)).trace = (dephase ρ * logm (dephase ρ)).trace :=
    trace_mul_of_isDiag _ _ (logm_isDiag (dephase_isDiag ρ))
  have h2 : (ρ * logm σ).trace = (dephase ρ * logm σ).trace :=
    trace_mul_of_isDiag _ _ (logm_isDiag hd)
  rw [relEntropy_eq_sub, relEntropy_eq_sub, relEntropy_eq_sub, h1, h2]
  ring

end Dephasing

/-- **Data-processing inequality** for the dephasing channel `dephase` (the von Neumann
measurement channel in the standard basis) and a reference state `σ` that is invariant
under it (i.e. is diagonal):

`D(Φ ρ ‖ Φ σ) ≤ D(ρ ‖ σ)`.
-/
