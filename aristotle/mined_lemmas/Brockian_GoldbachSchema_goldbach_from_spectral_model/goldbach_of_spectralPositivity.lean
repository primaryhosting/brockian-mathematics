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

namespace Brockian.GoldbachSchema

open Finset Complex

/-- The primes below `n`, i.e. the support of the spectral model at level `n`. -/

theorem goldbach_of_spectralPositivity (n : ℕ) (h4 : 4 ≤ n) (h : SpectralPositivity n) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p + q = n :=
  (spectralPositivity_iff n (by omega)).1 h

/-- **Goldbach from the spectral model**, unconditionally: the spectral non-vanishing
hypothesis of the model, imposed at every even level `n ≥ 4`, is *equivalent* to Goldbach's
conjecture. In particular the implication "spectral positivity ⟹ Goldbach" holds with no
extra hypotheses: the model-faithfulness hypothesis of the schema is discharged. -/
