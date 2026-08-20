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
noncomputable def singularSeries (n : ℕ) : ℝ :=
  ∏ p ∈ n.primeFactors.filter (fun p => p ≠ 2), (((p : ℝ) - 1) / ((p : ℝ) - 2))

/-- The finite set of Goldbach representations of `n`: primes `p ≤ n` such that `n - p`
is again prime. -/
def goldbachReps (n : ℕ) : Finset ℕ :=
  (Finset.range (n + 1)).filter (fun p => p.Prime ∧ (n - p).Prime)

/-- **Discharged hypothesis.** In the spectral schema this was carried as an extra
named assumption `main_pos : 0 < main`. It is in fact an unconditional theorem:
the singular series is a finite product of strictly positive rationals.

The Mathlib lemma that closes it is `Finset.prod_pos`. -/
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
theorem SpectralModel.main_pos {n : ℕ} (hn : 4 ≤ n) (M : SpectralModel n) : 0 < M.main := by
  have hn4 : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hlog : 0 < Real.log n := Real.log_pos (by linarith)
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  rw [M.main_def]
  exact mul_pos M.hc (mul_pos (singularSeries_pos n) (div_pos hn0 (pow_pos hlog 2)))

/-- **Goldbach from a spectral model.**
If `n ≥ 4` admits a spectral model, then `n` is a sum of two primes.
No further hypotheses are assumed: the positivity of the main term, which the schema
originally carried as a named open hypothesis, is discharged by `singularSeries_pos`. -/
theorem goldbach_from_spectral_model (n : ℕ) (hn : 4 ≤ n) (M : SpectralModel n) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p + q = n := by
  have hmain : 0 < M.main := M.main_pos hn
  have hR : 0 < M.R := by
    have h1 : -M.main < M.err := neg_lt_of_abs_lt M.err_lt
    have h2 := M.decomp
    linarith
  have hcard : 0 < ((goldbachReps n).card : ℝ) := lt_of_lt_of_le hR M.count_le
  have hcard' : 0 < (goldbachReps n).card := by exact_mod_cast hcard
  obtain ⟨p, hp⟩ := Finset.card_pos.mp hcard'
  rw [goldbachReps, Finset.mem_filter, Finset.mem_range] at hp
  obtain ⟨hlt, hpp, hq⟩ := hp
  exact ⟨p, n - p, hpp, hq, by omega⟩

/-- The schema in family form: a spectral model for every `n ≥ 4` yields Goldbach's
conjecture. -/
theorem goldbach_of_spectral_models (M : ∀ n : ℕ, 4 ≤ n → SpectralModel n) :
    ∀ n : ℕ, 4 ≤ n → Even n → ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p + q = n :=
  fun n hn _ => goldbach_from_spectral_model n hn (M n hn)

/-! ### Non-vacuity

The schema is not vacuous: a spectral model for `n` exists precisely when `n` has at least
one Goldbach representation. -/

/-- If `n ≥ 4` has a Goldbach representation, then it admits a spectral model. -/
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
theorem nonempty_spectralModel_100 : Nonempty (SpectralModel 100) :=
  nonempty_spectralModel_of_rep (p := 3) (q := 97) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)

end Brockian.GoldbachSchema

