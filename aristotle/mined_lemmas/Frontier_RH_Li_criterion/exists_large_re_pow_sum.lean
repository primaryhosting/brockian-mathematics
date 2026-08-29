/-
# RH Li Criterion
Category: Frontier — Moonshot
Target: Frontier.RH_Li_criterion
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# RH Li Criterion

Li's criterion in its finite (unconditional, purely arithmetic-geometric) form.

Let `Z` be a finite multiset of nonzero complex numbers ("the zeros", listed with
multiplicity) which is stable under the functional-equation symmetry `ρ ↦ 1 - ρ`.
The associated Li coefficients are

`λ n = ∑_{ρ ∈ Z} Re (1 - (1 - 1/ρ)^n)`.

The main theorem `Frontier.RH_Li_criterion` states the equivalence

`(∀ ρ ∈ Z, Re ρ = 1/2)  ↔  (∀ n ≥ 1, 0 ≤ λ n)`,

i.e. "all zeros lie on the critical line" iff "all Li coefficients are nonnegative".

The forward direction uses that `Re ρ = 1/2` is equivalent to `|1 - 1/ρ| = 1`; the reverse
direction uses the functional-equation symmetry to produce a zero with `|1 - 1/ρ| > 1`, and
then a simultaneous-recurrence (pigeonhole/compactness) argument showing that the power sums
`∑ (1 - 1/ρ)^n` are unbounded above along a sequence of exponents.

The criterion is then applied to the actual zeros of the Riemann zeta function:

* `Frontier.RH_Li_criterion_completedZeta`: for each `T`, the zeros of the Riemann xi
  function inside the box `0 ≤ Re s ≤ 1`, `|Im s| ≤ T` (a finite set) all lie on the
  critical line iff their Li coefficients are all nonnegative;
* `Frontier.RH_iff_liCoeff_nonneg`: the Riemann hypothesis — every zero of the completed
  zeta function `Λ` has real part `1/2` — holds iff, for every truncation height `T`, all
  Li coefficients of the corresponding finite family of zeros are nonnegative.

The classical Li coefficients, which are sums over *all* nontrivial zeros, require a
convergence theory (Hadamard factorisation of `ξ`) that is not developed here; the
equivalences above use the truncated families instead.
-/

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

set_option grind.warning false

namespace Frontier

open Complex Filter Finset

/-- The `n`-th Li coefficient attached to a multiset `Z` of "zeros":
`λ n = ∑_{ρ ∈ Z} Re (1 - (1 - 1/ρ)^n)`. -/

lemma exists_large_re_pow_sum {k : ℕ} (w : Fin k → ℂ) (hw : ∃ j, 1 < ‖w j‖) (C : ℝ) :
    ∃ n, 1 ≤ n ∧ C < (∑ j, w j ^ n).re := by
  obtain ⟨j0, hj0⟩ := hw
  have hne : (univ : Finset (Fin k)).Nonempty := ⟨j0, mem_univ _⟩
  set R := univ.sup' hne (fun j => ‖w j‖) with hRdef
  obtain ⟨jm, -, hjm⟩ := Finset.exists_mem_eq_sup' hne (fun j => ‖w j‖)
  have hRle : ∀ j, ‖w j‖ ≤ R := fun j => Finset.le_sup' (f := fun j => ‖w j‖) (mem_univ j)
  have hR1 : 1 < R := lt_of_lt_of_le hj0 (hRle j0)
  have hR0 : (0 : ℝ) < R := lt_trans zero_lt_one hR1
  have hjm' : ‖w jm‖ = R := hjm.symm
  set R' := univ.sup' hne (fun j => if ‖w j‖ = R then 0 else ‖w j‖) with hR'def
  have hR'lt : R' < R := by
    rw [hR'def, Finset.sup'_lt_iff]
    intro j _
    by_cases h : ‖w j‖ = R <;> simp [h] <;> [exact hR0; exact lt_of_le_of_ne (hRle j) h]
  have hR'0 : (0 : ℝ) ≤ R' := by
    have h := Finset.le_sup' (f := fun j => if ‖w j‖ = R then 0 else ‖w j‖) (mem_univ jm)
    rw [if_pos hjm'] at h
    exact h
  have hR'le : ∀ j, ‖w j‖ ≠ R → ‖w j‖ ≤ R' := by
    intro j hj
    have h := Finset.le_sup' (f := fun j => if ‖w j‖ = R then 0 else ‖w j‖) (mem_univ j)
    rw [if_neg hj] at h
    exact h
  -- the associated unit vectors
  set u : Fin k → ℂ := fun j => if ‖w j‖ = R then w j / (R : ℂ) else 1 with hudef
  have hRC : (R : ℂ) ≠ 0 := by exact_mod_cast hR0.ne'
  have hu : ∀ j, ‖u j‖ = 1 := by
    intro j
    by_cases h : ‖w j‖ = R
    · simp only [hudef, if_pos h, norm_div, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hR0, h]
      field_simp
    · simp [hudef, if_neg h]
  -- a threshold beyond which the maximal modulus dominates
  have h1 : Tendsto (fun n : ℕ => R ^ n) atTop atTop := tendsto_pow_atTop_atTop_of_one_lt hR1
  have h2 : Tendsto (fun n : ℕ => (R' / R) ^ n) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) ((div_lt_one hR0).mpr hR'lt)
  have e1 : ∀ᶠ n : ℕ in atTop, 4 * (|C| + 1) < R ^ n := h1.eventually_gt_atTop _
  have e2 : ∀ᶠ n : ℕ in atTop, (R' / R) ^ n < 1 / (4 * (k + 1)) :=
    h2.eventually_lt_const (by positivity)
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp (e1.and e2)
  obtain ⟨n, hnN, hn1, hnear⟩ := exists_pow_near_one u hu (ε := 1 / 2) (by norm_num) N₀
  obtain ⟨hC, hsmall⟩ := hN₀ n hnN
  refine ⟨n, hn1, ?_⟩
  have hRn : (0 : ℝ) < R ^ n := by positivity
  -- the terms of maximal modulus are all almost equal to `R ^ n`
  have hbig : ∀ j ∈ univ.filter (fun j => ‖w j‖ = R), R ^ n / 2 ≤ (w j ^ n).re := by
    intro j hj
    simp only [mem_filter] at hj
    have hwj : w j = (R : ℂ) * u j := by
      simp only [hudef, if_pos hj.2]
      field_simp
    have hpow : (w j) ^ n = ((R ^ n : ℝ) : ℂ) * (u j) ^ n := by
      rw [hwj, mul_pow]; push_cast; ring
    have h2' : (1 / 2 : ℝ) ≤ (u j ^ n).re := by
      have hn' := hnear j
      have h3 : (1 - u j ^ n).re ≤ ‖1 - u j ^ n‖ := Complex.re_le_norm _
      rw [norm_sub_rev] at h3
      simp at h3
      linarith
    rw [hpow, Complex.re_ofReal_mul]
    nlinarith
  -- the remaining terms are small
  have hsmallterm : ∀ j ∈ univ.filter (fun j => ¬ (‖w j‖ = R)), -(R' ^ n) ≤ (w j ^ n).re := by
    intro j hj
    simp only [mem_filter] at hj
    have h1' : |(w j ^ n).re| ≤ ‖w j ^ n‖ := Complex.abs_re_le_norm _
    have h2' : ‖w j ^ n‖ ≤ R' ^ n := by
      rw [norm_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) (hR'le j hj.2) n
    have h3' := abs_le.mp (le_trans h1' h2')
    linarith [h3'.1]
  have hsplit : (∑ j, w j ^ n).re
      = (∑ j ∈ univ.filter (fun j => ‖w j‖ = R), (w j ^ n).re)
        + (∑ j ∈ univ.filter (fun j => ¬ (‖w j‖ = R)), (w j ^ n).re) := by
    rw [Complex.re_sum, Finset.sum_filter_add_sum_filter_not]
  rw [hsplit]
  have hA : (1 : ℝ) ≤ (univ.filter (fun j => ‖w j‖ = R)).card := by
    have hmem : jm ∈ univ.filter (fun j => ‖w j‖ = R) := by simp [hjm']
    exact_mod_cast Finset.card_pos.mpr ⟨jm, hmem⟩
  have hAsum : R ^ n / 2 ≤ ∑ j ∈ univ.filter (fun j => ‖w j‖ = R), (w j ^ n).re := by
    have h := Finset.card_nsmul_le_sum (univ.filter (fun j => ‖w j‖ = R)) _ _ hbig
    rw [nsmul_eq_mul] at h
    nlinarith
  have hBsum :
      -((k : ℝ) * R' ^ n) ≤ ∑ j ∈ univ.filter (fun j => ¬ (‖w j‖ = R)), (w j ^ n).re := by
    have h := Finset.card_nsmul_le_sum (univ.filter (fun j => ¬ (‖w j‖ = R))) _ _ hsmallterm
    rw [nsmul_eq_mul] at h
    have hcard : ((univ.filter (fun j => ¬ (‖w j‖ = R))).card : ℝ) ≤ k := by
      have hc := Finset.card_filter_le (univ : Finset (Fin k)) (fun j => ¬ (‖w j‖ = R))
      simpa using (by exact_mod_cast hc :
        ((univ.filter (fun j => ¬ (‖w j‖ = R))).card : ℝ) ≤ ((univ : Finset (Fin k)).card : ℝ))
    have hR'n : (0 : ℝ) ≤ R' ^ n := by positivity
    nlinarith
  have hdom : (k : ℝ) * R' ^ n ≤ R ^ n / 4 := by
    have hR'n : R' ^ n = (R' / R) ^ n * R ^ n := by rw [div_pow]; field_simp
    have hlt : (R' / R) ^ n * R ^ n < 1 / (4 * ((k : ℝ) + 1)) * R ^ n :=
      mul_lt_mul_of_pos_right hsmall hRn
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    rw [hR'n]
    calc (k : ℝ) * ((R' / R) ^ n * R ^ n) ≤ (k : ℝ) * (1 / (4 * ((k : ℝ) + 1)) * R ^ n) :=
          mul_le_mul_of_nonneg_left hlt.le hk
      _ = ((k : ℝ) / ((k : ℝ) + 1)) * (R ^ n / 4) := by field_simp
      _ ≤ 1 * (R ^ n / 4) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact (div_le_one (by positivity)).mpr (by linarith)
      _ = R ^ n / 4 := one_mul _
  have hCR : C < R ^ n / 4 := by
    have habs : |C| < R ^ n / 4 := by linarith [abs_nonneg C]
    linarith [le_abs_self C]
  linarith

/-! ### The Li criterion -/

/-- Rewriting of `liCoeff` as a sum over an indexing of the multiset. -/
