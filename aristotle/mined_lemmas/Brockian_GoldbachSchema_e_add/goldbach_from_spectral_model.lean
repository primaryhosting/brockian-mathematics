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

theorem goldbach_from_spectral_model (hspec : SpectralModel) : Goldbach := by
  intro n hev h4
  have h := hspec n hev h4
  rw [spectralCount_eq_card] at h
  simp only [Complex.natCast_re] at h
  have hcard : 0 < (reps n).card := by exact_mod_cast h
  obtain ⟨pq, hpq⟩ := Finset.card_pos.mp hcard
  simp only [reps, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hpq
  exact ⟨pq.1, pq.2, hpq.2.1, hpq.2.2.1, hpq.2.2.2⟩

/-- The converse: Goldbach's conjecture implies the spectral model hypothesis. -/
