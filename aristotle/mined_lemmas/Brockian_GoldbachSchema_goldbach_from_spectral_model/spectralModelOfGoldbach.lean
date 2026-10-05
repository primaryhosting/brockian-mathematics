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
open scoped Nat

set_option maxHeartbeats 1000000

namespace Brockian
namespace GoldbachSchema

/-- `GoldbachPair n` says that `n` is a sum of two primes. -/

noncomputable def spectralModelOfGoldbach
    (h : ∀ n : ℕ, 4 ≤ n → Even n → GoldbachPair n) : SpectralModel where
  main := spectralCount
  err := fun _ => 0
  N₀ := 4
  decomposition := fun n => by simp
  dominates := fun n hn hev => by
    simpa using spectralCount_pos_of_goldbachPair (h n hn hev)

end GoldbachSchema
end Brockian

