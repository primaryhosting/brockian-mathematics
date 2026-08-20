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
open scoped Classical

namespace Brockian.GoldbachSchema

/-- The (finite, truncated) *singular series* factor attached to `n`:
the product of `(p-1)/(p-2)` over the odd prime divisors of `n`.
This is the arithmetic factor appearing in the circle-method main term for the
number of Goldbach representations of `n`. -/

theorem singularSeries_pos (n : ℕ) : 0 < singularSeries n := by
  refine Finset.prod_pos ?_
  intro p hp
  rw [Finset.mem_filter, Nat.mem_primeFactors] at hp
  obtain ⟨⟨hp2, -, -⟩, hne⟩ := hp
  have h3 : 3 ≤ p := by
    have := hp2.two_le
    omega
  have h3' : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast h3
  have h1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have h2 : (0 : ℝ) < (p : ℝ) - 2 := by linarith
  exact div_pos h1 h2

/-- A **spectral model** for the integer `n`: a circle-method style certificate
consisting of a spectral count `R` of Goldbach representations of `n`, split as a
main term (a positive multiple of the singular series times `n / (log n)^2`) plus an
error term which is dominated by the main term. -/
structure SpectralModel (n : ℕ) where
  /-- the implicit constant in the main term -/
  c : ℝ
  /-- positivity of the implicit constant -/
  hc : 0 < c
  /-- the spectral count of representations -/
  R : ℝ
  /-- the main term -/
  main : ℝ
  /-- the error term -/
  err : ℝ
  /-- the main term is the circle-method main term -/
  main_def : main = c * (singularSeries n * ((n : ℝ) / Real.log n ^ 2))
  /-- spectral decomposition of the count -/
  decomp : R = main + err
  /-- the error term is dominated by the main term -/
  err_lt : |err| < main
  /-- the spectral count is a lower bound for the true number of representations -/
  count_le : R ≤ (goldbachReps n).card

/-- The main term of a spectral model for `n ≥ 4` is strictly positive.
(This is the discharged sub-lemma `singularSeries_pos` in context.) -/
