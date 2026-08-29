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
# Goldbach From Spectral Model
Category: Brockian (Open Discharge)
Target: Brockian.GoldbachSchema.goldbach_from_spectral_model
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Goldbach From Spectral Model
Category: Brockian (Open Discharge)
Target: Brockian.GoldbachSchema.goldbach_from_spectral_model
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical

set_option maxHeartbeats 1000000

namespace Brockian.GoldbachSchema

noncomputable section

/-- The additive character `e(x) = exp(2πi x)` on the circle. -/

theorem spectralModel_iff_goldbach : SpectralModel ↔ Goldbach :=
  ⟨goldbach_from_spectral_model, spectralModel_of_goldbach⟩

end

/-
Note on the "open discharge" request.

`spectralModel_iff_goldbach` shows that the spectral model hypothesis `SpectralModel` is
*logically equivalent* to Goldbach's conjecture: by `spectralCount_eq_card` the spectral count
`spectralCount n` equals, exactly, the number of ordered pairs of primes summing to `n`.
Consequently, discharging the hypothesis of `goldbach_from_spectral_model` unconditionally would
be the same thing as proving Goldbach's conjecture, which is open.  What is proved here
unconditionally and axiom-cleanly is the reduction itself, together with the exact evaluation of
the circle-method (discrete Fourier) model that underlies it.
-/

end Brockian.GoldbachSchema

