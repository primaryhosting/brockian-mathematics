import Mathlib
/-!
# Area Law 1 D
Category: Frontier Phys
Target: Phys.area_law_1d
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(The header block is required to be the first content of the file; Lean 4 requires
`import` statements to precede every other command, including module docstrings, so the
single `import Mathlib` line above is the only thing preceding it.)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped ComplexOrder

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

namespace Phys

/-! ## Shannon entropy of a finite spectrum -/

/-- Shannon (von Neumann) entropy of a finite family of probabilities. -/

lemma schmidtSpectrum_nonneg [DecidableEq A] (psi : A → B → ℂ) (a : A) :
    0 ≤ schmidtSpectrum psi a :=
  (reducedDensity_posSemidef psi).eigenvalues_nonneg a

/-- For a normalized state the Schmidt spectrum is a probability vector. -/
