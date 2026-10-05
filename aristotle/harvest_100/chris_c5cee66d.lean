/-
# RH Li Criterion
Category: Frontier — Moonshot
Target: Frontier.RH_Li_criterion
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Complex Filter Metric

namespace Frontier

/-- The `n`-th Li coefficient attached to a (finite) multiset `Z` of "zeros":
`λ_n = ∑_{ρ ∈ Z} (1 - (1 - 1/ρ)^n)`. -/
noncomputable def liCoeff (Z : Multiset ℂ) (n : ℕ) : ℂ :=
  (Z.map (fun ρ => 1 - (1 - 1 / ρ) ^ n)).sum

lemma re_multiset_sum_map (Z : Multiset ℂ) (f : ℂ → ℂ) :
    ((Z.map f).sum).re = (Z.map (fun x => (f x).re)).sum := by
  induction Z using Multiset.induction_on with
  | empty => simp
  | cons a s ih => simp [ih]

lemma liCoeff_re (Z : Multiset ℂ) (n : ℕ) :
    (liCoeff Z n).re = (Z.map (fun ρ => 1 - ((1 - 1 / ρ) ^ n).re)).sum := by
  rw [liCoeff, re_multiset_sum_map]
  simp

/-- Reality of the Li coefficients for a multiset of zeros closed under complex conjugation. -/
lemma liCoeff_im_eq_zero (Z : Multiset ℂ) (hconj : Z.map (starRingEnd ℂ) = Z) (n : ℕ) :
    (liCoeff Z n).im = 0 := by
  have h : (starRingEnd ℂ) (liCoeff Z n) = liCoeff Z n := by
    rw [liCoeff, map_multiset_sum, Multiset.map_map]
    have hcomp : ((starRingEnd ℂ) ∘ fun ρ => 1 - (1 - 1 / ρ) ^ n)
        = (fun ρ => 1 - (1 - 1 / ρ) ^ n) ∘ (starRingEnd ℂ) := by
      funext ρ; simp
    rw [hcomp, ← Multiset.map_map, hconj]
  exact Complex.conj_eq_iff_im.mp h

/-- The Möbius transform `ρ ↦ 1 - 1/ρ` sends the closed half plane `Re ρ ≥ 1/2`
onto the closed unit disc. -/
lemma norm_one_sub_inv_le_one_iff {ρ : ℂ} (h0 : ρ ≠ 0) :
    ‖1 - 1 / ρ‖ ≤ 1 ↔ 1 / 2 ≤ ρ.re := by
  have hρ : ‖ρ‖ ≠ 0 := by simpa using h0
  have h1 : (1 : ℂ) - 1 / ρ = (ρ - 1) / ρ := by field_simp
  rw [h1, norm_div, div_le_one (by positivity)]
  rw [← Real.sqrt_sq (norm_nonneg (ρ - 1)), ← Real.sqrt_sq (norm_nonneg ρ)]
  rw [Real.sqrt_le_sqrt_iff (by positivity)]
  simp [Complex.sq_norm, Complex.normSq_apply]
  constructor <;> intro h <;> nlinarith [h]

lemma norm_pow_sub_one_le {u : ℂ} (hu : ‖u‖ ≤ 1) (t : ℕ) : ‖u ^ t - 1‖ ≤ t * ‖u - 1‖ := by
  rw [← geom_sum_mul u t, norm_mul]
  have h : ‖∑ i ∈ Finset.range t, u ^ i‖ ≤ t := by
    calc ‖∑ i ∈ Finset.range t, u ^ i‖ ≤ ∑ i ∈ Finset.range t, ‖u ^ i‖ := norm_sum_le _ _
      _ ≤ ∑ _i ∈ Finset.range t, (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro i _
          rw [norm_pow]
          exact pow_le_one₀ (norm_nonneg _) hu
      _ = t := by simp
  exact mul_le_mul_of_nonneg_right h (norm_nonneg _)

/-- Simultaneous Dirichlet approximation (one step): given finitely many complex numbers of
modulus one, some positive power brings them all simultaneously close to `1`. -/
lemma exists_pow_near_one_aux (s : Finset ℂ) (hs : ∀ u ∈ s, ‖u‖ = 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ d : ℕ, 1 ≤ d ∧ ∀ u ∈ s, ‖u ^ d - 1‖ < ε := by
  set x : ℕ → (↥s → ℂ) := fun n u => (u : ℂ) ^ n with hx
  have hmem : ∀ n, x n ∈ Metric.closedBall (0 : ↥s → ℂ) 1 := by
    intro n
    rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg zero_le_one]
    intro u
    simp [hx, norm_pow, hs u.1 u.2]
  obtain ⟨a, -, φ, hφ, htend⟩ := (isCompact_closedBall (0 : ↥s → ℂ) 1).tendsto_subseq hmem
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp htend.cauchySeq ε hε
  have hd : dist ((x ∘ φ) N) ((x ∘ φ) (N + 1)) < ε := hN N le_rfl (N + 1) (Nat.le_succ N)
  have hlt : φ N < φ (N + 1) := hφ (Nat.lt_succ_self N)
  refine ⟨φ (N + 1) - φ N, by omega, ?_⟩
  intro u hu
  have hu1 : ‖u‖ = 1 := hs u hu
  have hcoord := dist_le_pi_dist (x (φ N)) (x (φ (N + 1))) ⟨u, hu⟩
  have h2 : dist ((u : ℂ) ^ φ N) ((u : ℂ) ^ φ (N + 1)) < ε := lt_of_le_of_lt hcoord hd
  have hsplit : (u : ℂ) ^ φ (N + 1) = u ^ φ N * u ^ (φ (N + 1) - φ N) := by
    rw [← pow_add]; congr 1; omega
  rw [dist_eq_norm, hsplit, ← mul_one ((u : ℂ) ^ φ N), mul_assoc, ← mul_sub, norm_mul, one_mul,
    norm_pow, hu1, one_pow, one_mul] at h2
  rw [← norm_neg]
  simpa using h2

/-- Simultaneous Dirichlet approximation: arbitrarily large exponents work. -/
lemma exists_pow_near_one (s : Finset ℂ) (hs : ∀ u ∈ s, ‖u‖ = 1) {ε : ℝ} (hε : 0 < ε) (N : ℕ) :
    ∃ n : ℕ, N ≤ n ∧ 1 ≤ n ∧ ∀ u ∈ s, ‖u ^ n - 1‖ < ε := by
  set M := max N 1 with hM
  have hM1 : 1 ≤ M := le_max_right _ _
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM1
  obtain ⟨d, hd1, hd⟩ := exists_pow_near_one_aux s hs (div_pos hε hMpos)
  refine ⟨d * M, le_trans (le_max_left _ _) (Nat.le_mul_of_pos_left M hd1),
    Nat.one_le_iff_ne_zero.mpr (by positivity), ?_⟩
  intro u hu
  have h1 : ‖(u : ℂ) ^ d‖ ≤ 1 := by rw [norm_pow, hs u hu]; simp
  have h2 := norm_pow_sub_one_le h1 M
  rw [← pow_mul] at h2
  calc ‖u ^ (d * M) - 1‖ ≤ M * ‖u ^ d - 1‖ := h2
    _ < M * (ε / M) := mul_lt_mul_of_pos_left (hd u hu) hMpos
    _ = ε := by field_simp

/-- **Li's criterion** (finite abstract form, after Bombieri–Lagarias).

Let `Z` be a finite multiset of nonzero complex numbers ("the zeros"), closed under the
functional-equation symmetry `ρ ↦ 1 - ρ`.  Then all the elements of `Z` lie on the critical
line `Re ρ = 1/2` if and only if all the Li coefficients
`λ_n = ∑_{ρ ∈ Z} (1 - (1 - 1/ρ)^n)` are nonnegative for `n ≥ 1`. -/
theorem RH_Li_criterion (Z : Multiset ℂ) (h0 : (0 : ℂ) ∉ Z)
    (hfe : Z.map (fun ρ => 1 - ρ) = Z) :
    (∀ ρ ∈ Z, ρ.re = 1 / 2) ↔ ∀ n : ℕ, 1 ≤ n → 0 ≤ (liCoeff Z n).re := by
  constructor
  · -- Zeros on the critical line give `|1 - 1/ρ| = 1`, hence nonnegative Li coefficients.
    intro hline n _
    rw [liCoeff_re]
    refine Multiset.sum_nonneg ?_
    intro y hy
    obtain ⟨ρ, hρ, rfl⟩ := Multiset.mem_map.mp hy
    have hρ0 : ρ ≠ 0 := by rintro rfl; exact h0 hρ
    have hnorm : ‖1 - 1 / ρ‖ ≤ 1 := (norm_one_sub_inv_le_one_iff hρ0).mpr (hline ρ hρ).ge
    have h1 : ((1 - 1 / ρ) ^ n).re ≤ ‖(1 - 1 / ρ) ^ n‖ := Complex.re_le_norm _
    have h2 : ‖(1 - 1 / ρ) ^ n‖ ≤ 1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hnorm
    linarith
  · -- Conversely, a zero off the critical line produces a very negative Li coefficient.
    intro hpos ρ hρ
    by_contra hne
    -- By the functional-equation symmetry there is a zero strictly left of the critical line.
    obtain ⟨ρ₁, hρ₁Z, hρ₁re⟩ : ∃ ρ₁ ∈ Z, ρ₁.re < 1 / 2 := by
      rcases lt_or_gt_of_ne hne with h | h
      · exact ⟨ρ, hρ, h⟩
      · have hmem : (1 - ρ) ∈ Z := by
          have := Multiset.mem_map_of_mem (fun ρ => 1 - ρ) hρ
          rwa [hfe] at this
        exact ⟨1 - ρ, hmem, by simp; linarith⟩
    have hρ₁0 : ρ₁ ≠ 0 := by rintro rfl; exact h0 hρ₁Z
    set M := ‖1 - 1 / ρ₁‖ with hMdef
    have hM : 1 < M := by
      by_contra hc
      exact absurd ((norm_one_sub_inv_le_one_iff hρ₁0).mp (not_lt.mp hc)) (by linarith)
    -- the unit vectors in the directions of the numbers `1 - 1/ρ`
    set g : ℂ → ℂ := fun ρ => if (1 - 1 / ρ) = 0 then 1 else (1 - 1 / ρ) / ((‖1 - 1 / ρ‖ : ℝ) : ℂ)
      with hg
    set s : Finset ℂ := (Z.map g).toFinset with hsdef
    have hs : ∀ u ∈ s, ‖u‖ = 1 := by
      intro u hu
      rw [hsdef, Multiset.mem_toFinset] at hu
      obtain ⟨σ, hσ, rfl⟩ := Multiset.mem_map.mp hu
      by_cases hw : (1 - 1 / σ) = 0
      · simp only [hg]; rw [if_pos hw]; norm_num
      · simp only [hg]
        rw [if_neg hw, norm_div, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (norm_nonneg _), div_self (norm_ne_zero_iff.mpr hw)]
    obtain ⟨N, hN⟩ : ∃ N : ℕ, ((Z.card : ℝ) * 2) < M ^ N := pow_unbounded_of_one_lt _ hM
    obtain ⟨n, hnN, hn1, hnear⟩ := exists_pow_near_one s hs (by norm_num : (0 : ℝ) < 1 / 2) N
    -- for such an exponent every summand `Re ((1 - 1/σ)^n)` is at least `|1 - 1/σ|^n / 2`
    have key : ∀ σ ∈ Z, ‖1 - 1 / σ‖ ^ n / 2 ≤ ((1 - 1 / σ) ^ n).re := by
      intro σ hσ
      by_cases hw : (1 - 1 / σ) = 0
      · rw [hw]
        simp [zero_pow (by omega : n ≠ 0)]
      · have hus : g σ ∈ s := by
          rw [hsdef, Multiset.mem_toFinset]
          exact Multiset.mem_map_of_mem _ hσ
        have hgv : g σ = (1 - 1 / σ) / ((‖1 - 1 / σ‖ : ℝ) : ℂ) := by
          simp only [hg]; rw [if_neg hw]
        have hnc : ((‖1 - 1 / σ‖ : ℝ) : ℂ) ≠ 0 := by
          simpa using norm_ne_zero_iff.mpr hw
        have hfac : ((‖1 - 1 / σ‖ : ℝ) : ℂ) * g σ = 1 - 1 / σ := by
          rw [hgv, mul_comm, div_mul_cancel₀ _ hnc]
        have hre : (1 / 2 : ℝ) ≤ ((g σ) ^ n).re := by
          have h1 := hnear _ hus
          have h2 : (1 - (g σ) ^ n).re ≤ ‖1 - (g σ) ^ n‖ := Complex.re_le_norm _
          rw [show ‖1 - (g σ) ^ n‖ = ‖(g σ) ^ n - 1‖ from norm_sub_rev _ _] at h2
          simp only [Complex.sub_re, Complex.one_re] at h2
          linarith
        have hexp : ((1 - 1 / σ) ^ n).re = ‖1 - 1 / σ‖ ^ n * ((g σ) ^ n).re := by
          conv_lhs => rw [← hfac]
          rw [mul_pow, ← Complex.ofReal_pow, Complex.re_ofReal_mul]
        rw [hexp]
        have hpow : (0 : ℝ) ≤ ‖1 - 1 / σ‖ ^ n := by positivity
        nlinarith
    obtain ⟨Z', hZ'⟩ := Multiset.exists_cons_of_mem hρ₁Z
    have hsum : (liCoeff Z n).re ≤ (1 - M ^ n / 2) + Z'.card := by
      rw [liCoeff_re, hZ']
      simp only [Multiset.map_cons, Multiset.sum_cons]
      have h1 : 1 - ((1 - 1 / ρ₁) ^ n).re ≤ 1 - M ^ n / 2 := by
        have := key ρ₁ hρ₁Z
        rw [← hMdef] at this
        linarith
      have h2 : (Z'.map (fun σ => 1 - ((1 - 1 / σ) ^ n).re)).sum ≤ (Z'.card : ℝ) := by
        have h3 := Multiset.sum_le_card_nsmul (Z'.map (fun σ => 1 - ((1 - 1 / σ) ^ n).re)) 1 ?_
        · simpa using h3
        · intro y hy
          obtain ⟨σ, hσ, rfl⟩ := Multiset.mem_map.mp hy
          have hσZ : σ ∈ Z := by rw [hZ']; exact Multiset.mem_cons_of_mem hσ
          have h4 := key σ hσZ
          have hpow : (0 : ℝ) ≤ ‖1 - 1 / σ‖ ^ n := by positivity
          linarith
      linarith
    have hcard : (Z.card : ℝ) = (Z'.card : ℝ) + 1 := by
      rw [hZ']; push_cast [Multiset.card_cons]; ring
    have hMn : M ^ N ≤ M ^ n := pow_le_pow_right₀ (le_of_lt hM) hnN
    have hfin := hpos n hn1
    linarith

/-- **Li's criterion**, stated with genuinely real Li coefficients.

If in addition the multiset of zeros is closed under complex conjugation, then each `λ_n` is a
real number, and the criterion reads: all zeros lie on the critical line iff `λ_n ≥ 0` for all
`n ≥ 1`. -/
theorem RH_Li_criterion_real (Z : Multiset ℂ) (h0 : (0 : ℂ) ∉ Z)
    (hfe : Z.map (fun ρ => 1 - ρ) = Z) (hconj : Z.map (starRingEnd ℂ) = Z) :
    (∀ ρ ∈ Z, ρ.re = 1 / 2) ↔ ∀ n : ℕ, 1 ≤ n → ∃ l : ℝ, 0 ≤ l ∧ liCoeff Z n = (l : ℂ) := by
  constructor
  · intro hline n hn
    refine ⟨(liCoeff Z n).re, (RH_Li_criterion Z h0 hfe).mp hline n hn, ?_⟩
    apply Complex.ext <;> simp [liCoeff_im_eq_zero Z hconj n]
  · intro h
    refine (RH_Li_criterion Z h0 hfe).mpr ?_
    intro n hn
    obtain ⟨l, hl0, hl⟩ := h n hn
    rw [hl]
    simpa using hl0

end Frontier

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

