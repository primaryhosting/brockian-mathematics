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

lemma goldbachPair_of_spectralCount_pos {n : ℕ} (h : 0 < spectralCount n) :
    GoldbachPair n := by
  have hcard : 0 < (reps n).card := by
    have hne : ((reps n).card : ℝ) ≠ 0 := ne_of_gt h
    exact Nat.pos_of_ne_zero fun hz => hne (by simp [hz])
  obtain ⟨⟨p, q⟩, hx⟩ := Finset.card_pos.mp hcard
  exact ⟨p, q, mem_reps.mp hx⟩

/-- Conversely, a Goldbach representation makes the spectral count positive. -/
