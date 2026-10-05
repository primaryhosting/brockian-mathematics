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

lemma spectralCount_pos_of_goldbachPair {n : ℕ} (h : GoldbachPair n) :
    0 < spectralCount n := by
  obtain ⟨p, q, hp, hq, hpq⟩ := h
  have hmem : (p, q) ∈ reps n := mem_reps.mpr ⟨hp, hq, hpq⟩
  have hcard : 0 < (reps n).card := Finset.card_pos.mpr ⟨(p, q), hmem⟩
  have : (0 : ℝ) < ((reps n).card : ℝ) := by exact_mod_cast hcard
  simpa [spectralCount] using this

/--
A *spectral model* for the Goldbach problem: an analytic surrogate `main` for the
representation count, agreeing with the true spectral count up to an error term `err`
which is dominated by the main term for all even `n` beyond a threshold `N₀`.

This packages the (genuinely open) analytic input.  Everything else in this file is
unconditional.
-/
structure SpectralModel where
  /-- The spectral main term. -/
  main : ℕ → ℝ
  /-- The spectral error term. -/
  err : ℕ → ℝ
  /-- Threshold beyond which the model is claimed to be valid. -/
  N₀ : ℕ
  /-- The model reproduces the representation count exactly. -/
  decomposition : ∀ n : ℕ, spectralCount n = main n + err n
  /-- Beyond the threshold, the main term strictly dominates the error for even `n`. -/
  dominates : ∀ n : ℕ, N₀ ≤ n → Even n → |err n| < main n

/-- Above its threshold, a spectral model forces a positive representation count. -/
