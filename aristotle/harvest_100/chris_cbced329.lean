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
noncomputable def liCoeff (Z : Multiset ℂ) (n : ℕ) : ℝ :=
  (Z.map fun ρ => (1 - (1 - 1 / ρ) ^ n).re).sum

/-! ### The Cayley transform `ρ ↦ 1 - 1/ρ` -/

lemma norm_cayley_sq {ρ : ℂ} (hρ : ρ ≠ 0) :
    ‖1 - 1 / ρ‖ ^ 2 * ‖ρ‖ ^ 2 = ‖ρ‖ ^ 2 + 1 - 2 * ρ.re := by
  have h : (1 - 1 / ρ) * ρ = ρ - 1 := by field_simp
  have h2 : ‖1 - 1 / ρ‖ ^ 2 * ‖ρ‖ ^ 2 = ‖ρ - 1‖ ^ 2 := by rw [← h, norm_mul, mul_pow]
  rw [h2, Complex.sq_norm, Complex.sq_norm]
  simp [Complex.normSq_apply]
  ring

lemma cayley_sq_sub_one {ρ : ℂ} (hρ : ρ ≠ 0) :
    (‖1 - 1 / ρ‖ ^ 2 - 1) * ‖ρ‖ ^ 2 = 1 - 2 * ρ.re := by
  have := norm_cayley_sq hρ
  ring_nf
  ring_nf at this
  linarith

lemma norm_cayley_eq_one_iff {ρ : ℂ} (hρ : ρ ≠ 0) : ‖1 - 1 / ρ‖ = 1 ↔ ρ.re = 1 / 2 := by
  have key := cayley_sq_sub_one hρ
  have hP : 0 < ‖ρ‖ ^ 2 := by positivity
  have hn : 0 ≤ ‖1 - 1 / ρ‖ := norm_nonneg _
  constructor
  · intro h
    rw [h] at key
    simp at key
    linarith
  · intro h
    rw [h] at key
    have h1 : ‖1 - 1 / ρ‖ ^ 2 - 1 = 0 := by
      rcases mul_eq_zero.mp (by linarith : (‖1 - 1 / ρ‖ ^ 2 - 1) * ‖ρ‖ ^ 2 = 0) with h' | h'
      · exact h'
      · linarith
    have h2 : (‖1 - 1 / ρ‖ - 1) * (‖1 - 1 / ρ‖ + 1) = 0 := by nlinarith
    rcases mul_eq_zero.mp h2 with h' | h' <;> linarith

lemma one_lt_norm_cayley_iff {ρ : ℂ} (hρ : ρ ≠ 0) : 1 < ‖1 - 1 / ρ‖ ↔ ρ.re < 1 / 2 := by
  have key := cayley_sq_sub_one hρ
  have hP : 0 < ‖ρ‖ ^ 2 := by positivity
  have hn : 0 ≤ ‖1 - 1 / ρ‖ := norm_nonneg _
  constructor
  · intro h
    have hA : 0 < ‖1 - 1 / ρ‖ ^ 2 - 1 := by nlinarith
    nlinarith [mul_pos hA hP]
  · intro h
    by_contra hc
    push_neg at hc
    have hA : ‖1 - 1 / ρ‖ ^ 2 - 1 ≤ 0 := by nlinarith
    nlinarith [mul_nonpos_of_nonpos_of_nonneg hA hP.le]

/-! ### A recurrence lemma for finitely many rotations -/

/-- If `‖u^n - 1‖ ≤ δ` then `‖u^(t*n) - 1‖ ≤ t * δ`, for `u` on the unit circle. -/
lemma norm_pow_mul_sub_one_le {u : ℂ} (hu : ‖u‖ = 1) {n : ℕ} {δ : ℝ}
    (h : ‖u ^ n - 1‖ ≤ δ) (t : ℕ) : ‖u ^ (t * n) - 1‖ ≤ t * δ := by
  induction t with
  | zero => simp
  | succ t ih =>
    have hstep : u ^ ((t + 1) * n) - 1 = u ^ (t * n) * (u ^ n - 1) + (u ^ (t * n) - 1) := by
      ring_nf
    rw [hstep]
    have h1 : ‖u ^ (t * n)‖ = 1 := by rw [norm_pow, hu, one_pow]
    calc ‖u ^ (t * n) * (u ^ n - 1) + (u ^ (t * n) - 1)‖
        ≤ ‖u ^ (t * n) * (u ^ n - 1)‖ + ‖u ^ (t * n) - 1‖ := norm_add_le _ _
      _ ≤ δ + t * δ := by rw [norm_mul, h1, one_mul]; exact add_le_add h ih
      _ = ((t + 1 : ℕ) : ℝ) * δ := by push_cast; ring

/-- Simultaneous recurrence: finitely many unit complex numbers return simultaneously
close to `1` along some positive power. -/
lemma exists_pow_near_one_aux {k : ℕ} (u : Fin k → ℂ) (hu : ∀ j, ‖u j‖ = 1)
    {ε : ℝ} (hε : 0 < ε) : ∃ n, 1 ≤ n ∧ ∀ j, ‖u j ^ n - 1‖ ≤ ε := by
  have hs : IsCompact (Set.pi Set.univ (fun _ : Fin k => Metric.sphere (0 : ℂ) 1)) :=
    isCompact_univ_pi fun _ => isCompact_sphere 0 1
  have hmem : ∀ n : ℕ,
      (fun j => u j ^ n) ∈ Set.pi Set.univ (fun _ : Fin k => Metric.sphere (0 : ℂ) 1) := by
    intro n j _
    simp [norm_pow, hu j]
  obtain ⟨a, -, idx, hidx, hlim⟩ := hs.tendsto_subseq hmem
  have hcauchy : CauchySeq (fun m => (fun j => u j ^ idx m)) := hlim.cauchySeq
  rw [Metric.cauchySeq_iff] at hcauchy
  obtain ⟨N, hN⟩ := hcauchy ε hε
  have hlt := hN (N + 1) (by omega) N (le_refl N)
  rw [dist_pi_lt_iff hε] at hlt
  have hmono : idx N < idx (N + 1) := hidx (by omega)
  refine ⟨idx (N + 1) - idx N, by omega, fun j => ?_⟩
  have h1 : ‖u j ^ idx N‖ = 1 := by rw [norm_pow, hu j, one_pow]
  have h2 : u j ^ idx N * (u j ^ (idx (N + 1) - idx N) - 1) = u j ^ idx (N + 1) - u j ^ idx N := by
    rw [mul_sub, ← pow_add, mul_one, Nat.add_sub_cancel' hmono.le]
  have h4 := hlt j
  rw [Complex.dist_eq] at h4
  have h3 : ‖u j ^ (idx (N + 1) - idx N) - 1‖ = ‖u j ^ idx (N + 1) - u j ^ idx N‖ := by
    rw [← h2, norm_mul, h1, one_mul]
  rw [h3]
  exact h4.le

/-- Simultaneous recurrence with arbitrarily large exponent. -/
lemma exists_pow_near_one {k : ℕ} (u : Fin k → ℂ) (hu : ∀ j, ‖u j‖ = 1)
    {ε : ℝ} (hε : 0 < ε) (N : ℕ) : ∃ n, N ≤ n ∧ 1 ≤ n ∧ ∀ j, ‖u j ^ n - 1‖ ≤ ε := by
  set t : ℕ := max N 1 with ht
  have ht1 : 1 ≤ t := le_max_right _ _
  have htpos : (0 : ℝ) < t := by positivity
  obtain ⟨n₀, hn₀, hbd⟩ := exists_pow_near_one_aux u hu (ε := ε / t) (by positivity)
  refine ⟨t * n₀, ?_, ?_, fun j => ?_⟩
  · calc N ≤ t := le_max_left _ _
      _ = t * 1 := by ring
      _ ≤ t * n₀ := Nat.mul_le_mul_left t hn₀
  · exact Nat.one_le_iff_ne_zero.mpr (by positivity)
  · calc ‖u j ^ (t * n₀) - 1‖ ≤ (t : ℝ) * (ε / t) := norm_pow_mul_sub_one_le (hu j) (hbd j) t
      _ = ε := by field_simp

/-! ### Power sums of a finite family with an element of modulus `> 1` are unbounded -/

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
lemma liCoeff_eq (Z : Multiset ℂ) (n : ℕ) :
    liCoeff Z n =
      (Z.toList.length : ℝ) - (∑ i : Fin Z.toList.length, (1 - 1 / Z.toList[(i : ℕ)]) ^ n).re := by
  unfold liCoeff
  conv_lhs => rw [← Multiset.coe_toList Z]
  rw [Multiset.map_coe, Multiset.sum_coe, ← Fin.sum_univ_fun_getElem, Complex.re_sum]
  simp [Complex.sub_re, Finset.sum_sub_distrib]

/-- **Li's criterion** (finite form).  Let `Z` be a finite multiset of nonzero complex
numbers, stable under the symmetry `ρ ↦ 1 - ρ` of the functional equation.  Then all
elements of `Z` lie on the critical line `Re ρ = 1/2` if and only if all the Li
coefficients `liCoeff Z n`, `n ≥ 1`, are nonnegative. -/
theorem RH_Li_criterion (Z : Multiset ℂ) (hZ0 : ∀ ρ ∈ Z, ρ ≠ 0)
    (hfun : Z.map (fun ρ => 1 - ρ) = Z) :
    (∀ ρ ∈ Z, ρ.re = 1 / 2) ↔ ∀ n : ℕ, 1 ≤ n → 0 ≤ liCoeff Z n := by
  constructor
  · -- If every zero is on the critical line, every Cayley image lies on the unit circle,
    -- so each summand `Re (1 - z ^ n)` is nonnegative.
    intro h n _
    unfold liCoeff
    apply Multiset.sum_nonneg
    intro x hx
    obtain ⟨ρ, hρ, rfl⟩ := Multiset.mem_map.mp hx
    have h1 : ‖1 - 1 / ρ‖ = 1 := (norm_cayley_eq_one_iff (hZ0 ρ hρ)).mpr (h ρ hρ)
    have h2 : ‖(1 - 1 / ρ) ^ n‖ = 1 := by rw [norm_pow, h1, one_pow]
    have h3 : ((1 - 1 / ρ) ^ n).re ≤ 1 := le_trans (Complex.re_le_norm _) (le_of_eq h2)
    simp only [Complex.sub_re, Complex.one_re]
    linarith
  · -- Conversely, a zero off the critical line produces (using the functional equation) a
    -- Cayley image of modulus `> 1`, and then the power sums are unbounded.
    intro h
    by_contra hcon
    push_neg at hcon
    obtain ⟨ρ0, hρ0mem, hρ0⟩ := hcon
    obtain ⟨ρ1, hρ1mem, hρ1⟩ : ∃ ρ ∈ Z, ρ.re < 1 / 2 := by
      rcases lt_or_gt_of_ne hρ0 with h' | h'
      · exact ⟨ρ0, hρ0mem, h'⟩
      · refine ⟨1 - ρ0, ?_, ?_⟩
        · rw [← hfun]
          exact Multiset.mem_map_of_mem _ hρ0mem
        · simp only [Complex.sub_re, Complex.one_re]
          linarith
    have hmem : ρ1 ∈ Z.toList := by rwa [Multiset.mem_toList]
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp hmem
    have hw : ∃ j : Fin Z.toList.length,
        1 < ‖(fun i : Fin Z.toList.length => 1 - 1 / Z.toList[(i : ℕ)]) j‖ := by
      refine ⟨i, ?_⟩
      have hget : Z.toList[(i : ℕ)] = ρ1 := by rw [← hi]; simp
      simp only [hget]
      exact (one_lt_norm_cayley_iff (hZ0 ρ1 hρ1mem)).mpr hρ1
    obtain ⟨n, hn1, hlarge⟩ := exists_large_re_pow_sum
      (fun i : Fin Z.toList.length => 1 - 1 / Z.toList[(i : ℕ)]) hw (Z.toList.length : ℝ)
    have hc := h n hn1
    rw [liCoeff_eq] at hc
    linarith

/-! ### Non-vacuity: both sides of the criterion do occur -/

/-- A pair of "zeros" on the critical line, `1/2 ± i`: it satisfies the hypotheses of
`RH_Li_criterion`, hence all its Li coefficients are nonnegative. -/
theorem liCoeff_nonneg_of_critical_pair :
    ∀ n : ℕ, 1 ≤ n → 0 ≤ liCoeff {(1 / 2 + Complex.I), (1 / 2 - Complex.I)} n := by
  refine (RH_Li_criterion _ ?_ ?_).mp ?_
  · intro ρ hρ
    simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hρ
    rcases hρ with rfl | rfl <;> intro h <;>
      · have := congrArg Complex.re h
        simp at this
  · show ((1 - (1 / 2 + Complex.I)) ::ₘ (1 - (1 / 2 - Complex.I)) ::ₘ 0 : Multiset ℂ) = _
    rw [show (1 - (1 / 2 + Complex.I) : ℂ) = 1 / 2 - Complex.I by ring,
      show (1 - (1 / 2 - Complex.I) : ℂ) = 1 / 2 + Complex.I by ring]
    exact Multiset.cons_swap _ _ _
  · intro ρ hρ
    simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hρ
    rcases hρ with rfl | rfl <;> simp

/-- A pair of "zeros" off the critical line, `1/4` and `3/4`: it satisfies the hypotheses of
`RH_Li_criterion`, so some Li coefficient must be negative. -/
theorem exists_liCoeff_neg_of_offCriticalLine :
    ∃ n : ℕ, 1 ≤ n ∧ liCoeff {(1 / 4 : ℂ), (3 / 4 : ℂ)} n < 0 := by
  have h0 : ∀ ρ ∈ ({(1 / 4 : ℂ), (3 / 4 : ℂ)} : Multiset ℂ), ρ ≠ 0 := by
    intro ρ hρ
    simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hρ
    rcases hρ with rfl | rfl <;> norm_num
  have hf : Multiset.map (fun ρ : ℂ => 1 - ρ) {(1 / 4 : ℂ), (3 / 4 : ℂ)}
      = {(1 / 4 : ℂ), (3 / 4 : ℂ)} := by
    show ((1 - (1 / 4 : ℂ)) ::ₘ (1 - (3 / 4 : ℂ)) ::ₘ 0 : Multiset ℂ) = _
    rw [show (1 - (1 / 4 : ℂ)) = 3 / 4 by ring, show (1 - (3 / 4 : ℂ)) = 1 / 4 by ring]
    exact Multiset.cons_swap _ _ _
  have hoff : ¬ ∀ ρ ∈ ({(1 / 4 : ℂ), (3 / 4 : ℂ)} : Multiset ℂ), ρ.re = 1 / 2 := by
    intro h
    have h1 := h (1 / 4) (by simp)
    norm_num at h1
  have h2 := mt (RH_Li_criterion _ h0 hf).mpr hoff
  push_neg at h2
  exact h2

/-! ### Application to the zeros of the completed Riemann zeta function

We apply the criterion to the (finitely many) zeros of the Riemann xi function inside a
symmetric box `0 ≤ Re s ≤ 1`, `|Im s| ≤ T`.  The Riemann xi function is realised in the
entire form `ξ(s) = s (1 - s) Λ(s) = s (1 - s) Λ₀(s) - 1`, where `Λ` is Mathlib's
`completedRiemannZeta` and `Λ₀` is `completedRiemannZeta₀`; away from `s = 0, 1` its zeros
are exactly the zeros of `Λ`, i.e. the nontrivial zeros of `ζ`. -/

/-- The Riemann xi function `ξ(s) = s (1 - s) Λ(s)`, written in a manifestly entire form. -/
noncomputable def riemannXi (s : ℂ) : ℂ := s * (1 - s) * completedRiemannZeta₀ s - 1

lemma differentiable_riemannXi : Differentiable ℂ riemannXi := by
  unfold riemannXi
  exact ((differentiable_id.mul ((differentiable_const (c := (1 : ℂ))).sub differentiable_id)).mul
    differentiable_completedZeta₀).sub_const 1

@[simp] lemma riemannXi_zero : riemannXi 0 = -1 := by simp [riemannXi]

@[simp] lemma riemannXi_one : riemannXi 1 = -1 := by simp [riemannXi]

/-- The functional equation `ξ(1 - s) = ξ(s)`. -/
lemma riemannXi_one_sub (s : ℂ) : riemannXi (1 - s) = riemannXi s := by
  simp only [riemannXi, completedRiemannZeta₀_one_sub]
  ring_nf

lemma riemannXi_eq_mul {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) :
    riemannXi s = s * (1 - s) * completedRiemannZeta s := by
  have h1' : (1 - s) ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
  rw [completedRiemannZeta_eq, riemannXi]
  field_simp
  ring

/-- Away from `s = 0, 1`, the zeros of `ξ` are exactly the zeros of the completed zeta
function, i.e. the nontrivial zeros of `ζ`. -/
lemma riemannXi_eq_zero_iff {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) :
    riemannXi s = 0 ↔ completedRiemannZeta s = 0 := by
  have h1' : (1 - s) ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
  rw [riemannXi_eq_mul h0 h1, mul_eq_zero, mul_eq_zero]
  simp [h0, h1']

/-- There are only finitely many zeros of `ξ` in the box `0 ≤ Re s ≤ 1`, `|Im s| ≤ T`. -/
lemma zetaZeros_finite (T : ℝ) :
    {s : ℂ | riemannXi s = 0 ∧ 0 ≤ s.re ∧ s.re ≤ 1 ∧ |s.im| ≤ T}.Finite := by
  by_contra hinf
  have hinf' : {s : ℂ | riemannXi s = 0 ∧ 0 ≤ s.re ∧ s.re ≤ 1 ∧ |s.im| ≤ T}.Infinite := hinf
  have hK : IsCompact {s : ℂ | 0 ≤ s.re ∧ s.re ≤ 1 ∧ |s.im| ≤ T} := by
    apply Metric.isCompact_of_isClosed_isBounded
    · refine IsClosed.inter (isClosed_le continuous_const Complex.continuous_re) ?_
      exact IsClosed.inter (isClosed_le Complex.continuous_re continuous_const)
        (isClosed_le Complex.continuous_im.abs continuous_const)
    · apply Bornology.IsBounded.subset (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := 1 + |T|))
      intro s hs
      obtain ⟨h1, h2, h3⟩ := hs
      simp only [Metric.mem_closedBall, dist_zero_right]
      have hb := Complex.norm_le_abs_re_add_abs_im s
      have hre : |s.re| ≤ 1 := abs_le.mpr ⟨by linarith, h2⟩
      have him : |s.im| ≤ |T| := le_trans h3 (le_abs_self T)
      linarith
  obtain ⟨x, -, hacc⟩ := hinf'.exists_accPt_of_subset_isCompact hK fun s hs => hs.2
  rw [accPt_iff_frequently_nhdsNE] at hacc
  have hfreq : ∃ᶠ z in nhdsWithin x {x}ᶜ, riemannXi z = 0 := hacc.mono fun z hz => hz.1
  have hanal : AnalyticOnNhd ℂ riemannXi Set.univ :=
    differentiable_riemannXi.differentiableOn.analyticOnNhd isOpen_univ
  have heq := hanal.eqOn_zero_of_preconnected_of_frequently_eq_zero isPreconnected_univ
    (Set.mem_univ x) hfreq
  have hx0 := heq (Set.mem_univ 0)
  rw [riemannXi_zero] at hx0
  simp at hx0

/-- The zeros of `ξ` in the box `0 ≤ Re s ≤ 1`, `|Im s| ≤ T`, as a finite multiset. -/
noncomputable def zetaZeroMultiset (T : ℝ) : Multiset ℂ := (zetaZeros_finite T).toFinset.val

lemma mem_zetaZeroMultiset {T : ℝ} {s : ℂ} :
    s ∈ zetaZeroMultiset T ↔ riemannXi s = 0 ∧ 0 ≤ s.re ∧ s.re ≤ 1 ∧ |s.im| ≤ T := by
  rw [zetaZeroMultiset, Finset.mem_val, Set.Finite.mem_toFinset]
  rfl

/-- **Li's criterion for the Riemann xi function, truncated to a symmetric box.**
All zeros of `ξ` (equivalently, all nontrivial zeros of `ζ`) in the box `0 ≤ Re s ≤ 1`,
`|Im s| ≤ T` lie on the critical line if and only if all the Li coefficients of that finite
family of zeros are nonnegative.  The Riemann hypothesis is the statement that the left-hand
side holds for every `T`. -/
theorem RH_Li_criterion_completedZeta (T : ℝ) :
    (∀ s : ℂ, riemannXi s = 0 → 0 ≤ s.re → s.re ≤ 1 → |s.im| ≤ T → s.re = 1 / 2)
      ↔ ∀ n : ℕ, 1 ≤ n → 0 ≤ liCoeff (zetaZeroMultiset T) n := by
  have h0 : ∀ ρ ∈ zetaZeroMultiset T, ρ ≠ 0 := by
    intro ρ hρ hzero
    rw [mem_zetaZeroMultiset] at hρ
    rw [hzero, riemannXi_zero] at hρ
    simpa using hρ.1
  have hstab : ∀ s : ℂ, s ∈ (zetaZeros_finite T).toFinset ↔
      (1 - s) ∈ (zetaZeros_finite T).toFinset := by
    intro s
    simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq, riemannXi_one_sub, Complex.sub_re,
      Complex.sub_im, Complex.one_re, Complex.one_im, zero_sub, abs_neg]
    constructor
    · rintro ⟨h1, h2, h3, h4⟩
      exact ⟨h1, by linarith, by linarith, h4⟩
    · rintro ⟨h1, h2, h3, h4⟩
      exact ⟨h1, by linarith, by linarith, h4⟩
  have hfun : (zetaZeroMultiset T).map (fun ρ => 1 - ρ) = zetaZeroMultiset T := by
    have hinj : Set.InjOn (fun ρ : ℂ => 1 - ρ) ((zetaZeros_finite T).toFinset : Set ℂ) := by
      intro a _ b _ hab
      simpa using sub_right_injective hab
    rw [zetaZeroMultiset, ← Finset.image_val_of_injOn hinj]
    congr 1
    ext x
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (hstab y).mp hy
    · intro hx
      exact ⟨1 - x, (hstab x).mp hx, by ring⟩
  rw [← RH_Li_criterion (zetaZeroMultiset T) h0 hfun]
  constructor
  · intro h ρ hρ
    rw [mem_zetaZeroMultiset] at hρ
    exact h ρ hρ.1 hρ.2.1 hρ.2.2.1 hρ.2.2.2
  · intro h s h1 h2 h3 h4
    exact h s (mem_zetaZeroMultiset.mpr ⟨h1, h2, h3, h4⟩)

/-! ### The Riemann hypothesis itself -/

lemma completedZeta_ne_zero_of_one_le_re {s : ℂ} (h : 1 ≤ s.re) :
    completedRiemannZeta s ≠ 0 := by
  have hs0 : s ≠ 0 := by
    intro hc
    rw [hc] at h
    simp at h
    linarith
  have h1 : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_le_re h
  rw [riemannZeta_def_of_ne_zero hs0] at h1
  intro hz
  rw [hz] at h1
  simp at h1

/-- Every zero of the completed zeta function lies in the open critical strip. -/
lemma completedZeta_zero_mem_strip {s : ℂ} (h : completedRiemannZeta s = 0) :
    0 < s.re ∧ s.re < 1 := by
  constructor
  · by_contra hc
    push_neg at hc
    have h1 : 1 ≤ (1 - s).re := by
      simp only [Complex.sub_re, Complex.one_re]
      linarith
    exact completedZeta_ne_zero_of_one_le_re h1 (by rw [completedRiemannZeta_one_sub]; exact h)
  · by_contra hc
    push_neg at hc
    exact completedZeta_ne_zero_of_one_le_re hc h

/-- **The Riemann hypothesis is equivalent to the nonnegativity of all Li coefficients.**

The left-hand side is the Riemann hypothesis: every zero of the completed zeta function
`Λ` (equivalently, every nontrivial zero of `ζ`) has real part `1/2`.  The right-hand side
says that for every truncation height `T`, all Li coefficients `λ n`, `n ≥ 1`, of the finite
family of zeros with `|Im s| ≤ T` are nonnegative. -/
theorem RH_iff_liCoeff_nonneg :
    (∀ s : ℂ, completedRiemannZeta s = 0 → s.re = 1 / 2)
      ↔ ∀ T : ℝ, ∀ n : ℕ, 1 ≤ n → 0 ≤ liCoeff (zetaZeroMultiset T) n := by
  constructor
  · intro h T
    refine (RH_Li_criterion_completedZeta T).mp ?_
    intro s hxi _ _ _
    have hs0 : s ≠ 0 := by rintro rfl; simp at hxi
    have hs1 : s ≠ 1 := by rintro rfl; simp at hxi
    exact h s ((riemannXi_eq_zero_iff hs0 hs1).mp hxi)
  · intro h s hs
    obtain ⟨hlo, hhi⟩ := completedZeta_zero_mem_strip hs
    have hs0 : s ≠ 0 := by rintro rfl; simp at hlo
    have hs1 : s ≠ 1 := by rintro rfl; simp at hhi
    have hxi : riemannXi s = 0 := (riemannXi_eq_zero_iff hs0 hs1).mpr hs
    exact (RH_Li_criterion_completedZeta |s.im|).mpr (h |s.im|) s hxi hlo.le hhi.le (le_refl _)

end Frontier

