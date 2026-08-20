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

theorem nonempty_spectralModel_of_rep {n p q : ℕ} (hn : 4 ≤ n) (hp : p.Prime) (hq : q.Prime)
    (hpq : p + q = n) : Nonempty (SpectralModel n) := by
  have hn4 : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hlog : 0 < Real.log n := Real.log_pos (by linarith)
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  set A : ℝ := singularSeries n * ((n : ℝ) / Real.log n ^ 2) with hA
  have hApos : 0 < A := mul_pos (singularSeries_pos n) (div_pos hn0 (pow_pos hlog 2))
  have hmem : p ∈ goldbachReps n := by
    rw [goldbachReps, Finset.mem_filter, Finset.mem_range]
    refine ⟨by omega, hp, ?_⟩
    have hnp : n - p = q := by omega
    rw [hnp]; exact hq
  have hcard : 0 < (goldbachReps n).card := Finset.card_pos.mpr ⟨p, hmem⟩
  have hcard' : (1 : ℝ) ≤ ((goldbachReps n).card : ℝ) := by exact_mod_cast hcard
  exact ⟨{ c := A⁻¹
           hc := inv_pos.mpr hApos
           R := 1
           main := 1
           err := 0
           main_def := by rw [← hA, inv_mul_cancel₀ (ne_of_gt hApos)]
           decomp := by norm_num
           err_lt := by norm_num
           count_le := hcard' }⟩

/-- A concrete witness: `100 = 3 + 97` gives a spectral model for `100`. -/
