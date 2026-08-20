/-
# RH Li Criterion
Category: Frontier — Moonshot
Target: Frontier.RH_Li_criterion
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean requires `import` to precede any module docstring, so the header above is repeated
-- verbatim as the module docstring below.)

import Mathlib

/-!
# RH Li Criterion
Category: Frontier — Moonshot
Target: Frontier.RH_Li_criterion
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
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

namespace Frontier

open Complex Filter

/-!
## Elementary complex-analytic estimates
-/

/-- Geometric bound: `|1 - r ^ n| ≤ n |1 - r| max(1,r) ^ n` for real `r ≥ 0`. -/
theorem real_geom_bound (r : ℝ) (hr : 0 ≤ r) (n : ℕ) :
    |1 - r ^ n| ≤ n * |1 - r| * (max 1 r) ^ n := by
  have h : 1 - r ^ n = (1 - r) * ∑ i ∈ Finset.range n, r ^ i := by
    have h2 : (∑ i ∈ Finset.range n, r ^ i) * (r - 1) = r ^ n - 1 := geom_sum_mul r n
    linear_combination h2
  rw [h, abs_mul]
  have hM : (1 : ℝ) ≤ max 1 r := le_max_left _ _
  have hs : |∑ i ∈ Finset.range n, r ^ i| ≤ n * (max 1 r) ^ n := by
    calc |∑ i ∈ Finset.range n, r ^ i| ≤ ∑ i ∈ Finset.range n, |r ^ i| :=
          Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range n, (max 1 r) ^ n := by
        refine Finset.sum_le_sum fun i hi => ?_
        rw [abs_pow, abs_of_nonneg hr]
        exact (pow_le_pow_left₀ hr (le_max_right _ _) i).trans
          (pow_le_pow_right₀ hM (Finset.mem_range.mp hi).le)
    _ = n * (max 1 r) ^ n := by simp
  calc |1 - r| * |∑ i ∈ Finset.range n, r ^ i| ≤ |1 - r| * (n * (max 1 r) ^ n) :=
        mul_le_mul_of_nonneg_left hs (abs_nonneg _)
  _ = n * |1 - r| * (max 1 r) ^ n := by ring

/-- `‖1 - w ^ n‖ ≤ n ‖1 - w‖` for `‖w‖ ≤ 1`. -/
theorem norm_one_sub_pow_le (w : ℂ) (hw : ‖w‖ ≤ 1) (n : ℕ) : ‖1 - w ^ n‖ ≤ n * ‖1 - w‖ := by
  have h : 1 - w ^ n = (1 - w) * ∑ i ∈ Finset.range n, w ^ i := by
    have h2 : (∑ i ∈ Finset.range n, w ^ i) * (w - 1) = w ^ n - 1 := geom_sum_mul w n
    linear_combination h2
  rw [h, norm_mul]
  have hs : ‖∑ i ∈ Finset.range n, w ^ i‖ ≤ n := by
    calc ‖∑ i ∈ Finset.range n, w ^ i‖ ≤ ∑ i ∈ Finset.range n, ‖w ^ i‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ Finset.range n, 1 := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hw
    _ = n := by simp
  calc ‖1 - w‖ * ‖∑ i ∈ Finset.range n, w ^ i‖ ≤ ‖1 - w‖ * n :=
        mul_le_mul_of_nonneg_left hs (norm_nonneg _)
  _ = n * ‖1 - w‖ := by ring

/-- `‖w ^ n - 1‖ ≤ n ‖w - 1‖` for `‖w‖ ≤ 1`. -/
theorem norm_pow_sub_one_le (w : ℂ) (hw : ‖w‖ ≤ 1) (n : ℕ) : ‖w ^ n - 1‖ ≤ n * ‖w - 1‖ := by
  have h1 : ‖w ^ n - 1‖ = ‖1 - w ^ n‖ := by rw [← norm_neg]; congr 1; ring
  have h2 : ‖w - 1‖ = ‖1 - w‖ := by rw [← norm_neg]; congr 1; ring
  rw [h1, h2]
  exact norm_one_sub_pow_le w hw n

/-- For a unit complex number, `1 - Re (w ^ n) ≤ n ^ 2 (1 - Re w)`. -/
theorem unit_re_pow_bound (w : ℂ) (hw : ‖w‖ = 1) (n : ℕ) :
    1 - (w ^ n).re ≤ (n : ℝ) ^ 2 * (1 - w.re) := by
  have key : ∀ v : ℂ, ‖v‖ = 1 → 1 - v.re = ‖1 - v‖ ^ 2 / 2 := by
    intro v hv
    have h2 : Complex.normSq v = 1 := by
      have := Complex.sq_norm v; rw [hv] at this; simpa using this.symm
    rw [Complex.sq_norm]
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.one_re, Complex.sub_im,
      Complex.one_im, zero_sub, neg_mul] at h2 ⊢
    nlinarith [h2]
  have hwn : ‖w ^ n‖ = 1 := by rw [norm_pow, hw, one_pow]
  rw [key _ hwn, key _ hw]
  have h1 := norm_one_sub_pow_le w hw.le n
  have h0 : (0 : ℝ) ≤ ‖1 - w‖ := norm_nonneg _
  have h2 : (0 : ℝ) ≤ ‖1 - w ^ n‖ := norm_nonneg _
  nlinarith [h1, h0, h2, sq_nonneg ((n : ℝ) * ‖1 - w‖ - ‖1 - w ^ n‖)]

/-- Master estimate. With `d = 1 - Re z` and `e = max 0 (‖z‖ - 1)`,
`|1 - Re (z ^ n)| ≤ 2 n ^ 2 (1 + e) ^ n (d + 2 e)` for all `n ≥ 1`. -/
theorem master_bound (z : ℂ) (n : ℕ) (hn : 1 ≤ n) :
    |1 - (z ^ n).re| ≤
      2 * (n : ℝ) ^ 2 * (1 + max 0 (‖z‖ - 1)) ^ n * ((1 - z.re) + 2 * max 0 (‖z‖ - 1)) := by
  rcases eq_or_ne z 0 with rfl | hz
  · have hz0 : ((0 : ℂ) ^ n).re = 0 := by rw [zero_pow (by omega)]; simp
    rw [hz0]
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    simp only [norm_zero, Complex.zero_re, sub_zero, zero_sub]
    have hmx : max (0 : ℝ) (-1) = 0 := by norm_num
    rw [hmx]
    simp only [add_zero, one_pow, mul_one, mul_zero]
    rw [abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1)]
    nlinarith
  set r : ℝ := ‖z‖ with hrdef
  have hr0 : 0 < r := norm_pos_iff.mpr hz
  have hrne : (r : ℂ) ≠ 0 := by exact_mod_cast hr0.ne'
  set w : ℂ := z / (r : ℂ) with hwdef
  have hw1 : ‖w‖ = 1 := by
    rw [hwdef, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0, ← hrdef,
      div_self hr0.ne']
  have hzw : z = (r : ℂ) * w := by rw [hwdef]; field_simp
  have hzre : z.re = r * w.re := by rw [hzw]; simp
  have hzpow : (z ^ n).re = r ^ n * (w ^ n).re := by
    rw [hzw, mul_pow, ← Complex.ofReal_pow, Complex.re_ofReal_mul]
  set e : ℝ := max 0 (r - 1) with hedef
  set d : ℝ := 1 - z.re with hddef
  set u : ℝ := 1 - w.re with hudef
  have he0 : 0 ≤ e := le_max_left _ _
  have hu0 : 0 ≤ u := by
    have : w.re ≤ ‖w‖ := Complex.re_le_norm w
    rw [hw1] at this; simp only [hudef]; linarith
  have hd : d = 1 - r + r * u := by rw [hddef, hzre, hudef]; ring
  have hde : 0 ≤ d + e := by
    have h1 : r - 1 ≤ e := le_max_right _ _
    nlinarith [mul_nonneg hr0.le hu0]
  have hR : max 1 r = 1 + e := by
    rcases le_total r 1 with h | h
    · rw [max_eq_left h, hedef, max_eq_left (by linarith)]; ring
    · rw [max_eq_right h, hedef, max_eq_right (by linarith)]; ring
  have hRpos : (0 : ℝ) < 1 + e := by linarith
  have hrR : r ≤ 1 + e := hR ▸ le_max_right _ _
  have h1r : |1 - r| ≤ d + 2 * e := by
    rcases le_total r 1 with h | h
    · rw [abs_of_nonneg (by linarith)]
      nlinarith [mul_nonneg hr0.le hu0]
    · rw [abs_of_nonpos (by linarith)]
      have : e = r - 1 := by rw [hedef, max_eq_right (by linarith)]
      linarith
  have hrnu : r ^ n * u ≤ (1 + e) ^ n * (d + 2 * e) := by
    rcases le_total r 1 with h | h
    · have he : e = 0 := by rw [hedef, max_eq_left (by linarith)]
      have hrn : r ^ n ≤ r := by
        calc r ^ n ≤ r ^ 1 := pow_le_pow_of_le_one hr0.le h hn
        _ = r := pow_one r
      have h2 : r ^ n * u ≤ r * u := mul_le_mul_of_nonneg_right hrn hu0
      rw [he]; simp only [add_zero, one_pow, one_mul, mul_zero]
      nlinarith
    · have he : e = r - 1 := by rw [hedef, max_eq_right (by linarith)]
      have hru : r * u = d + e := by rw [hd, he]; ring
      have hrn1 : r ^ n ≤ (1 + e) ^ n * r := by
        have hh : r ^ n = r ^ (n - 1) * r := by rw [← pow_succ]; congr 1; omega
        rw [hh]
        apply mul_le_mul_of_nonneg_right _ hr0.le
        calc r ^ (n - 1) ≤ (1 + e) ^ (n - 1) := pow_le_pow_left₀ hr0.le hrR _
        _ ≤ (1 + e) ^ n := pow_le_pow_right₀ (by linarith) (by omega)
      calc r ^ n * u ≤ ((1 + e) ^ n * r) * u := mul_le_mul_of_nonneg_right hrn1 hu0
      _ = (1 + e) ^ n * (r * u) := by ring
      _ = (1 + e) ^ n * (d + e) := by rw [hru]
      _ ≤ (1 + e) ^ n * (d + 2 * e) :=
          mul_le_mul_of_nonneg_left (by linarith) (pow_nonneg hRpos.le _)
  have hsplit : 1 - (z ^ n).re = (1 - r ^ n) + r ^ n * (1 - (w ^ n).re) := by rw [hzpow]; ring
  have hwn0 : 0 ≤ 1 - (w ^ n).re := by
    have : (w ^ n).re ≤ ‖w ^ n‖ := Complex.re_le_norm _
    rw [norm_pow, hw1, one_pow] at this; linarith
  have hwn : 1 - (w ^ n).re ≤ (n : ℝ) ^ 2 * u := unit_re_pow_bound w hw1 n
  have hgeom := real_geom_bound r hr0.le n
  rw [hR] at hgeom
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hstep1 : |1 - (z ^ n).re| ≤ |1 - r ^ n| + r ^ n * (1 - (w ^ n).re) := by
    rw [hsplit]
    calc |1 - r ^ n + r ^ n * (1 - (w ^ n).re)| ≤ |1 - r ^ n| + |r ^ n * (1 - (w ^ n).re)| :=
          abs_add_le _ _
    _ = |1 - r ^ n| + r ^ n * (1 - (w ^ n).re) := by
        rw [abs_of_nonneg (mul_nonneg (pow_nonneg hr0.le _) hwn0)]
  have hA : |1 - r ^ n| ≤ (n : ℝ) * ((1 + e) ^ n * (d + 2 * e)) := by
    refine hgeom.trans ?_
    have h3 := mul_le_mul_of_nonneg_left h1r (by positivity : (0 : ℝ) ≤ (n : ℝ))
    have h4 := mul_le_mul_of_nonneg_right h3 (pow_nonneg hRpos.le n)
    calc (n : ℝ) * |1 - r| * (1 + e) ^ n ≤ (n : ℝ) * (d + 2 * e) * (1 + e) ^ n := h4
    _ = (n : ℝ) * ((1 + e) ^ n * (d + 2 * e)) := by ring
  have hB : r ^ n * (1 - (w ^ n).re) ≤ (n : ℝ) ^ 2 * ((1 + e) ^ n * (d + 2 * e)) := by
    calc r ^ n * (1 - (w ^ n).re) ≤ r ^ n * ((n : ℝ) ^ 2 * u) :=
          mul_le_mul_of_nonneg_left hwn (pow_nonneg hr0.le _)
    _ = (n : ℝ) ^ 2 * (r ^ n * u) := by ring
    _ ≤ (n : ℝ) ^ 2 * ((1 + e) ^ n * (d + 2 * e)) :=
        mul_le_mul_of_nonneg_left hrnu (by positivity)
  have hpos : 0 ≤ (1 + e) ^ n * (d + 2 * e) := mul_nonneg (pow_nonneg hRpos.le _) (by linarith)
  have hnn : (n : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
  have hlast := mul_le_mul_of_nonneg_right hnn hpos
  calc |1 - (z ^ n).re| ≤ |1 - r ^ n| + r ^ n * (1 - (w ^ n).re) := hstep1
  _ ≤ (n : ℝ) * ((1 + e) ^ n * (d + 2 * e)) + (n : ℝ) ^ 2 * ((1 + e) ^ n * (d + 2 * e)) := by
      linarith
  _ ≤ (n : ℝ) ^ 2 * ((1 + e) ^ n * (d + 2 * e)) + (n : ℝ) ^ 2 * ((1 + e) ^ n * (d + 2 * e)) := by
      linarith
  _ = 2 * (n : ℝ) ^ 2 * (1 + e) ^ n * (d + 2 * e) := by ring

/-- Simultaneous recurrence (a Dirichlet-type approximation statement): finitely many unit
complex numbers can be simultaneously brought within `ε` of `1` by a common, arbitrarily
large power. -/
theorem simultaneous_recurrence (s : Finset ℕ) (w : ℕ → ℂ) (hw : ∀ k ∈ s, ‖w k‖ = 1)
    (ε : ℝ) (hε : 0 < ε) (N : ℕ) : ∃ n, N ≤ n ∧ 1 ≤ n ∧ ∀ k ∈ s, ‖w k ^ n - 1‖ ≤ ε := by
  have key : ∀ δ : ℝ, 0 < δ → ∃ p, 1 ≤ p ∧ ∀ k ∈ s, ‖w k ^ p - 1‖ ≤ δ := by
    intro δ hδ
    set X : ℕ → (∀ i : {k // k ∈ s}, ℂ) := fun n i => (w i.1) ^ n with hX
    have hmem : ∀ n, X n ∈ Metric.closedBall (0 : ∀ i : {k // k ∈ s}, ℂ) 1 := by
      intro n
      rw [Metric.mem_closedBall, dist_zero_right]
      refine (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun i => ?_
      rw [hX]
      simp only [norm_pow]
      rw [hw i.1 i.2, one_pow]
    obtain ⟨a, -, psi, hpsi, hlim⟩ :=
      (isCompact_closedBall (0 : ∀ i : {k // k ∈ s}, ℂ) 1).tendsto_subseq hmem
    rw [Metric.tendsto_atTop] at hlim
    obtain ⟨M, hM⟩ := hlim (δ / 2) (by linarith)
    have h1 := hM M le_rfl
    have h2 := hM (M + 1) (by omega)
    have hlt : psi M < psi (M + 1) := hpsi (Nat.lt_succ_self M)
    have hd : dist (X (psi M)) (X (psi (M + 1))) < δ := by
      calc dist (X (psi M)) (X (psi (M + 1))) ≤ dist (X (psi M)) a + dist a (X (psi (M + 1))) :=
            dist_triangle _ _ _
      _ < δ / 2 + δ / 2 := by rw [dist_comm a]; exact add_lt_add h1 h2
      _ = δ := by ring
    refine ⟨psi (M + 1) - psi M, by omega, fun k hk => ?_⟩
    have hcoord : dist ((X (psi M)) ⟨k, hk⟩) ((X (psi (M + 1))) ⟨k, hk⟩)
        ≤ dist (X (psi M)) (X (psi (M + 1))) := dist_le_pi_dist _ _ _
    have heq : ‖w k ^ (psi M) - w k ^ (psi (M + 1))‖ = ‖w k ^ (psi (M + 1) - psi M) - 1‖ := by
      have e1 : w k ^ (psi (M + 1)) = w k ^ (psi M) * w k ^ (psi (M + 1) - psi M) := by
        rw [← pow_add, Nat.add_sub_cancel' hlt.le]
      rw [e1]
      have e2 : w k ^ (psi M) - w k ^ (psi M) * w k ^ (psi (M + 1) - psi M)
           = w k ^ (psi M) * (1 - w k ^ (psi (M + 1) - psi M)) := by ring
      rw [e2, norm_mul, norm_pow, hw k hk, one_pow, one_mul, ← norm_neg]
      congr 1; ring
    rw [dist_eq_norm] at hcoord
    have h4 : ‖w k ^ (psi M) - w k ^ (psi (M + 1))‖ ≤ dist (X (psi M)) (X (psi (M + 1))) := hcoord
    rw [heq] at h4
    linarith
  obtain ⟨p, hp1, hp⟩ := key (ε / (N + 1)) (by positivity)
  refine ⟨(N + 1) * p, by nlinarith, by nlinarith, fun k hk => ?_⟩
  have h1 : ‖(w k ^ p) ^ (N + 1) - 1‖ ≤ (N + 1 : ℕ) * ‖w k ^ p - 1‖ := by
    apply norm_pow_sub_one_le
    rw [norm_pow, hw k hk, one_pow]
  rw [← pow_mul] at h1
  have hcomm : p * (N + 1) = (N + 1) * p := by ring
  rw [hcomm] at h1
  have h2 : ((N : ℝ) + 1) * ‖w k ^ p - 1‖ ≤ ((N : ℝ) + 1) * (ε / (N + 1)) :=
    mul_le_mul_of_nonneg_left (hp k hk) (by positivity)
  have h3 : ((N : ℝ) + 1) * (ε / (N + 1)) = ε := by field_simp
  push_cast at h1
  linarith

/-!
## The abstract positivity criterion

Given a family `z : ℕ → ℂ` we consider the "Li sums" `∑' k, Re (1 - (z k) ^ n)`.
Under natural summability hypotheses, all these sums are nonnegative if and only if
every `z k` lies in the closed unit disc.
-/

/-- The Li-type sum attached to a family of complex numbers. -/
noncomputable def liSumOf (z : ℕ → ℂ) (n : ℕ) : ℝ := ∑' k, (1 - (z k) ^ n).re

/-- The summability majorant attached to a family. -/
noncomputable def liMajorant (z : ℕ → ℂ) (k : ℕ) : ℝ :=
  (1 - (z k).re) + 2 * max 0 (‖z k‖ - 1)

theorem liMajorant_nonneg (z : ℕ → ℂ) (k : ℕ) : 0 ≤ liMajorant z k := by
  have h1 : (z k).re ≤ ‖z k‖ := Complex.re_le_norm _
  have h2 : ‖z k‖ - 1 ≤ max 0 (‖z k‖ - 1) := le_max_right _ _
  have h3 : (0 : ℝ) ≤ max 0 (‖z k‖ - 1) := le_max_left _ _
  simp only [liMajorant]
  linarith

theorem summable_liMajorant {z : ℕ → ℂ} (hd : Summable fun k => 1 - (z k).re)
    (he : Summable fun k => max 0 (‖z k‖ - 1)) : Summable (liMajorant z) :=
  hd.add (he.mul_left 2)

/-- Summability of the terms of the Li sum. -/
theorem summable_liTerms {z : ℕ → ℂ} (hd : Summable fun k => 1 - (z k).re)
    (he : Summable fun k => max 0 (‖z k‖ - 1)) (n : ℕ) :
    Summable fun k => (1 - (z k) ^ n).re := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  set E : ℝ := ∑' k, max 0 (‖z k‖ - 1) with hE
  have hEk : ∀ k, max 0 (‖z k‖ - 1) ≤ E := fun k => he.le_tsum k fun i _ => le_max_left _ _
  have hE0 : 0 ≤ E := le_trans (le_max_left 0 _) (hEk 0)
  refine Summable.of_norm_bounded
    (g := fun k => (2 * (n : ℝ) ^ 2 * (1 + E) ^ n) * liMajorant z k)
    ((summable_liMajorant hd he).mul_left _) fun k => ?_
  have hmb := master_bound (z k) n hn
  have hnorm : ‖(1 - (z k) ^ n).re‖ = |1 - ((z k) ^ n).re| := by
    simp [Real.norm_eq_abs]
  rw [hnorm]
  refine hmb.trans ?_
  have hstep : (1 + max 0 (‖z k‖ - 1)) ^ n ≤ (1 + E) ^ n :=
    pow_le_pow_left₀ (by positivity) (by linarith [hEk k]) n
  have h2 : 2 * (n : ℝ) ^ 2 * (1 + max 0 (‖z k‖ - 1)) ^ n ≤ 2 * (n : ℝ) ^ 2 * (1 + E) ^ n :=
    mul_le_mul_of_nonneg_left hstep (by positivity)
  have h3 := mul_le_mul_of_nonneg_right h2 (liMajorant_nonneg z k)
  simpa [liMajorant] using h3

/-- Easy direction: if all `z k` lie in the closed unit disc then all Li sums are `≥ 0`. -/
theorem liSumOf_nonneg_of_norm_le_one {z : ℕ → ℂ} (h : ∀ k, ‖z k‖ ≤ 1) (n : ℕ) :
    0 ≤ liSumOf z n := by
  refine tsum_nonneg fun k => ?_
  have h1 : ((z k) ^ n).re ≤ ‖(z k) ^ n‖ := Complex.re_le_norm _
  have h2 : ‖(z k) ^ n‖ ≤ 1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) (h k)
  simp only [Complex.sub_re, Complex.one_re]
  linarith

/-- Only finitely many members of the family can have norm `≥ 1 + η`. -/
theorem finite_large_norm {z : ℕ → ℂ} (he : Summable fun k => max 0 (‖z k‖ - 1)) {η : ℝ}
    (hη : 0 < η) : {k | 1 + η ≤ ‖z k‖}.Finite := by
  have h0 := he.tendsto_cofinite_zero
  have h1 : ∀ᶠ k in cofinite, max 0 (‖z k‖ - 1) < η := h0 (Iio_mem_nhds hη)
  rw [Filter.eventually_cofinite] at h1
  refine Set.Finite.subset h1 fun k hk => ?_
  simp only [Set.mem_setOf_eq] at hk ⊢
  push_neg
  have h2 : η ≤ ‖z k‖ - 1 := by linarith
  exact h2.trans (le_max_right _ _)

/-- If some member of the family lies outside the closed unit disc, the supremum of the norms
is attained. -/
theorem exists_max_norm {z : ℕ → ℂ} (he : Summable fun k => max 0 (‖z k‖ - 1)) {j : ℕ}
    (hj : 1 < ‖z j‖) : ∃ M : ℝ, 1 < M ∧ (∃ k, ‖z k‖ = M) ∧ ∀ k, ‖z k‖ ≤ M := by
  set η : ℝ := (‖z j‖ - 1) / 2 with hηdef
  have hη : 0 < η := by rw [hηdef]; linarith
  have hfin := finite_large_norm he hη
  set S : Finset ℕ := hfin.toFinset with hS
  have hjS : j ∈ S := by
    rw [hS, Set.Finite.mem_toFinset]
    simp only [Set.mem_setOf_eq, hηdef]
    linarith
  obtain ⟨k0, hk0S, hk0⟩ := S.exists_max_image (fun k => ‖z k‖) ⟨j, hjS⟩
  refine ⟨‖z k0‖, lt_of_lt_of_le hj (hk0 j hjS), ⟨k0, rfl⟩, fun k => ?_⟩
  by_cases hk : k ∈ S
  · exact hk0 k hk
  · rw [hS, Set.Finite.mem_toFinset] at hk
    simp only [Set.mem_setOf_eq, not_le] at hk
    have hjk : ‖z j‖ ≤ ‖z k0‖ := hk0 j hjS
    rw [hηdef] at hk
    linarith

/-- There is a gap below the maximal norm: the indices attaining the maximum form a
nonempty finite set `F`, and all other members have norm at most some `M' < M`. -/
theorem exists_gap {z : ℕ → ℂ} (he : Summable fun k => max 0 (‖z k‖ - 1)) {M : ℝ}
    (hM1 : 1 < M) (hMle : ∀ k, ‖z k‖ ≤ M) (hMex : ∃ k, ‖z k‖ = M) :
    ∃ (F : Finset ℕ) (M' : ℝ), F.Nonempty ∧ (∀ k ∈ F, ‖z k‖ = M) ∧ 1 ≤ M' ∧ M' < M ∧
      ∀ k, k ∉ F → ‖z k‖ ≤ M' := by
  set η : ℝ := (M - 1) / 2 with hηdef
  have hη : 0 < η := by rw [hηdef]; linarith
  have hfin := finite_large_norm he hη
  set S : Finset ℕ := hfin.toFinset with hS
  have hmemS : ∀ k, k ∈ S ↔ 1 + η ≤ ‖z k‖ := by
    intro k; rw [hS, Set.Finite.mem_toFinset]; rfl
  obtain ⟨k1, hk1⟩ := hMex
  have hk1S : k1 ∈ S := by rw [hmemS, hk1, hηdef]; linarith
  set F : Finset ℕ := S.filter (fun k => ‖z k‖ = M) with hF
  set G : Finset ℕ := S.filter (fun k => ‖z k‖ ≠ M) with hG
  have hFne : F.Nonempty := ⟨k1, by rw [hF, Finset.mem_filter]; exact ⟨hk1S, hk1⟩⟩
  set Gv : Finset ℝ := insert (1 + η) (G.image fun k => ‖z k‖) with hGv
  have hGvne : Gv.Nonempty := ⟨1 + η, by rw [hGv]; exact Finset.mem_insert_self _ _⟩
  set M' : ℝ := Gv.max' hGvne with hM'
  have hM'mem : M' ∈ Gv := Gv.max'_mem hGvne
  have hηM' : 1 + η ≤ M' := Gv.le_max' _ (by rw [hGv]; exact Finset.mem_insert_self _ _)
  refine ⟨F, M', hFne, ?_, by linarith, ?_, ?_⟩
  · intro k hk; rw [hF, Finset.mem_filter] at hk; exact hk.2
  · rw [hGv, Finset.mem_insert] at hM'mem
    rcases hM'mem with hcase | hcase
    · rw [hcase, hηdef]; linarith
    · rw [Finset.mem_image] at hcase
      obtain ⟨k, hkG, hkv⟩ := hcase
      rw [hG, Finset.mem_filter] at hkG
      exact hkv ▸ lt_of_le_of_ne (hMle k) hkG.2
  · intro k hkF
    by_cases hkS : k ∈ S
    · have hne : ‖z k‖ ≠ M := fun hcontra =>
        hkF (by rw [hF, Finset.mem_filter]; exact ⟨hkS, hcontra⟩)
      have hkG : k ∈ G := by rw [hG, Finset.mem_filter]; exact ⟨hkS, hne⟩
      exact Gv.le_max' _
        (by rw [hGv]; exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hkG))
    · rw [hmemS] at hkS
      push_neg at hkS
      linarith

/-- The contribution of the indices outside `F` to the Li sum is at most `2 n^2 M'^n T`. -/
theorem tail_bound {z : ℕ → ℂ} (hd : Summable fun k => 1 - (z k).re)
    (he : Summable fun k => max 0 (‖z k‖ - 1)) (F : Finset ℕ) (M' : ℝ) (hM'1 : 1 ≤ M')
    (hout : ∀ k, k ∉ F → ‖z k‖ ≤ M') (n : ℕ) (hn : 1 ≤ n) :
    ∑' k : ((F : Set ℕ)ᶜ : Set ℕ), (1 - (z k) ^ n).re
      ≤ 2 * (n : ℝ) ^ 2 * M' ^ n * (∑' k, liMajorant z k) := by
  set c : ℝ := 2 * (n : ℝ) ^ 2 * M' ^ n with hc
  have hc0 : 0 ≤ c := by
    have hM'n : (0 : ℝ) ≤ M' ^ n := pow_nonneg (by linarith) n
    rw [hc]; positivity
  set g : ℕ → ℝ := fun k => c * liMajorant z k with hg
  have hgsum : Summable g := (summable_liMajorant hd he).mul_left c
  have hg0 : ∀ k, 0 ≤ g k := fun k => mul_nonneg hc0 (liMajorant_nonneg z k)
  have hle : ∀ k : ((F : Set ℕ)ᶜ : Set ℕ), (1 - (z k.1) ^ n).re ≤ g k.1 := by
    rintro ⟨k, hk⟩
    simp only [Set.mem_compl_iff, Finset.mem_coe] at hk
    have hmb := master_bound (z k) n hn
    have hb : (1 - (z k) ^ n).re ≤ |1 - ((z k) ^ n).re| := by
      simp only [Complex.sub_re, Complex.one_re]
      exact le_abs_self _
    refine hb.trans (hmb.trans ?_)
    have hstep : (1 + max 0 (‖z k‖ - 1)) ^ n ≤ M' ^ n := by
      apply pow_le_pow_left₀ (by positivity)
      rcases le_total (‖z k‖) 1 with hcase | hcase
      · rw [max_eq_left (by linarith)]; linarith
      · rw [max_eq_right (by linarith)]
        have := hout k hk
        linarith
    have h2 : 2 * (n : ℝ) ^ 2 * (1 + max 0 (‖z k‖ - 1)) ^ n ≤ c := by
      rw [hc]; exact mul_le_mul_of_nonneg_left hstep (by positivity)
    have h3 := mul_le_mul_of_nonneg_right h2 (liMajorant_nonneg z k)
    simpa [hg, liMajorant] using h3
  calc ∑' k : ((F : Set ℕ)ᶜ : Set ℕ), (1 - (z k) ^ n).re
      ≤ ∑' k : ((F : Set ℕ)ᶜ : Set ℕ), g k :=
        Summable.tsum_le_tsum hle ((summable_liTerms hd he n).subtype _) (hgsum.subtype _)
  _ ≤ ∑' k, g k := hgsum.tsum_subtype_le g _ hg0
  _ = 2 * (n : ℝ) ^ 2 * M' ^ n * (∑' k, liMajorant z k) := by rw [hg, tsum_mul_left]

/-- Hard direction: nonnegativity of all Li sums forces all `z k` into the closed unit disc. -/
theorem norm_le_one_of_liSumOf_nonneg {z : ℕ → ℂ} (hd : Summable fun k => 1 - (z k).re)
    (he : Summable fun k => max 0 (‖z k‖ - 1)) (h : ∀ n : ℕ, 1 ≤ n → 0 ≤ liSumOf z n) (k : ℕ) :
    ‖z k‖ ≤ 1 := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨M, hM1, hMex, hMle⟩ := exists_max_norm he hcon
  obtain ⟨F, M', hFne, hFM, hM'1, hM'M, hout⟩ := exists_gap he hM1 hMle hMex
  set T : ℝ := ∑' k, liMajorant z k with hT
  have hT0 : 0 ≤ T := tsum_nonneg (liMajorant_nonneg z)
  have hM0 : (0 : ℝ) < M := by linarith
  have hMC : (M : ℂ) ≠ 0 := by exact_mod_cast hM0.ne'
  have hcard1 : (1 : ℝ) ≤ (F.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hFne
  have hlim : Tendsto (fun n : ℕ =>
      (F.card : ℝ) * (M⁻¹) ^ n + 2 * T * ((n : ℝ) ^ 2 * (M' / M) ^ n)) atTop (nhds 0) := by
    have h1 : Tendsto (fun n : ℕ => (F.card : ℝ) * (M⁻¹) ^ n) atTop (nhds 0) := by
      have hb : |M⁻¹| < 1 := by
        rw [abs_of_pos (by positivity), inv_lt_one_iff₀]
        exact Or.inr hM1
      simpa using (tendsto_pow_atTop_nhds_zero_of_abs_lt_one hb).const_mul ((F.card : ℝ))
    have h2 : Tendsto (fun n : ℕ => 2 * T * ((n : ℝ) ^ 2 * (M' / M) ^ n)) atTop (nhds 0) := by
      have hb : |M' / M| < 1 := by
        rw [abs_of_nonneg (by positivity), div_lt_one hM0]
        exact hM'M
      simpa using (tendsto_pow_const_mul_const_pow_of_abs_lt_one 2 hb).const_mul (2 * T)
    simpa using h1.add h2
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hlim.eventually_lt_const (by norm_num : (0 : ℝ) < 1 / 2))
  have hwunit : ∀ j ∈ F, ‖z j / (M : ℂ)‖ = 1 := by
    intro j hj
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hM0, hFM j hj, div_self hM0.ne']
  obtain ⟨n, hnN, hn1, hrec⟩ :=
    simultaneous_recurrence F (fun j => z j / (M : ℂ)) hwunit 1 one_pos N
  have hFbound : ∀ j ∈ F, (1 - (z j) ^ n).re ≤ 1 - M ^ n / 2 := by
    intro j hj
    have hu : ‖(z j / (M : ℂ))‖ = 1 := hwunit j hj
    have hun : ‖(z j / (M : ℂ)) ^ n‖ = 1 := by rw [norm_pow, hu, one_pow]
    have hrecj := hrec j hj
    set v : ℂ := (z j / (M : ℂ)) ^ n with hv
    have hre : (1 : ℝ) / 2 ≤ v.re := by
      have h2 : ‖v - 1‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg (v - 1)]
      rw [Complex.sq_norm] at h2
      simp only [Complex.normSq_apply, Complex.sub_re, Complex.one_re, Complex.sub_im,
        Complex.one_im, sub_zero] at h2
      have h3 : Complex.normSq v = 1 := by
        have := Complex.sq_norm v; rw [hun] at this; simpa using this.symm
      simp only [Complex.normSq_apply] at h3
      nlinarith
    have hzj : (z j) ^ n = (M : ℂ) ^ n * v := by
      rw [hv, div_pow]; field_simp
    have hzre : ((z j) ^ n).re = M ^ n * v.re := by
      rw [hzj, ← Complex.ofReal_pow, Complex.re_ofReal_mul]
    simp only [Complex.sub_re, Complex.one_re, hzre]
    have hMn : (0 : ℝ) < M ^ n := pow_pos hM0 n
    nlinarith
  have hsum := (summable_liTerms hd he n).sum_add_tsum_compl (s := F)
  have htail := tail_bound hd he F M' hM'1 hout n hn1
  have hFsum : ∑ j ∈ F, (1 - (z j) ^ n).re ≤ (F.card : ℝ) * (1 - M ^ n / 2) := by
    calc ∑ j ∈ F, (1 - (z j) ^ n).re ≤ ∑ _j ∈ F, (1 - M ^ n / 2) := Finset.sum_le_sum hFbound
    _ = (F.card : ℝ) * (1 - M ^ n / 2) := by rw [Finset.sum_const, nsmul_eq_mul]
  have hpos := h n hn1
  rw [liSumOf, ← hsum] at hpos
  have hMn : (0 : ℝ) < M ^ n := pow_pos hM0 n
  have hkey := hN n hnN
  have hmul : ((F.card : ℝ) * (M⁻¹) ^ n + 2 * T * ((n : ℝ) ^ 2 * (M' / M) ^ n)) * M ^ n
      = (F.card : ℝ) + 2 * (n : ℝ) ^ 2 * M' ^ n * T := by
    have h1 : (M⁻¹) ^ n * M ^ n = 1 := by rw [← mul_pow, inv_mul_cancel₀ hM0.ne', one_pow]
    have h2 : (M' / M) ^ n * M ^ n = M' ^ n := by
      rw [div_pow, div_mul_cancel₀ _ (pow_ne_zero n hM0.ne')]
    calc ((F.card : ℝ) * (M⁻¹) ^ n + 2 * T * ((n : ℝ) ^ 2 * (M' / M) ^ n)) * M ^ n
        = (F.card : ℝ) * ((M⁻¹) ^ n * M ^ n)
          + 2 * T * (n : ℝ) ^ 2 * ((M' / M) ^ n * M ^ n) := by ring
    _ = (F.card : ℝ) + 2 * (n : ℝ) ^ 2 * M' ^ n * T := by rw [h1, h2]; ring
  have hfinal : (F.card : ℝ) + 2 * (n : ℝ) ^ 2 * M' ^ n * T < M ^ n / 2 := by
    have h4 := mul_lt_mul_of_pos_right hkey hMn
    rw [hmul] at h4
    calc (F.card : ℝ) + 2 * (n : ℝ) ^ 2 * M' ^ n * T < 1 / 2 * M ^ n := h4
    _ = M ^ n / 2 := by ring
  have hcardM : (F.card : ℝ) * (1 - M ^ n / 2) ≤ (F.card : ℝ) - M ^ n / 2 := by nlinarith
  linarith

/-- **Abstract positivity criterion** (the analytic core of Li's criterion, in the spirit of
Bombieri--Lagarias): under the two summability hypotheses, all Li sums of the family are
nonnegative if and only if every member of the family lies in the closed unit disc. -/
theorem liSumOf_nonneg_iff {z : ℕ → ℂ} (hd : Summable fun k => 1 - (z k).re)
    (he : Summable fun k => max 0 (‖z k‖ - 1)) :
    (∀ k, ‖z k‖ ≤ 1) ↔ ∀ n : ℕ, 1 ≤ n → 0 ≤ liSumOf z n :=
  ⟨fun h n _ => liSumOf_nonneg_of_norm_le_one h n, fun h => norm_le_one_of_liSumOf_nonneg hd he h⟩

/-!
## The Riemann zeta function
-/

/-- The set of nontrivial zeros of the Riemann zeta function, i.e. the zeros excluded from
the statement of `RiemannHypothesis` in Mathlib. -/
def nontrivialZeros : Set ℂ :=
  {s | riemannZeta s = 0 ∧ (¬∃ n : ℕ, s = -2 * (n + 1)) ∧ s ≠ 1}

theorem riemannHypothesis_iff : RiemannHypothesis ↔ ∀ s ∈ nontrivialZeros, s.re = 1 / 2 := by
  constructor
  · rintro h s ⟨h1, h2, h3⟩
    exact h s h1 h2 h3
  · intro h s h1 h2 h3
    exact h s ⟨h1, h2, h3⟩

theorem ne_zero_of_mem_nontrivialZeros {s : ℂ} (hs : s ∈ nontrivialZeros) : s ≠ 0 := by
  rintro rfl
  have := hs.1
  rw [riemannZeta_zero] at this
  norm_num at this

/-- The set of nontrivial zeros is stable under `s ↦ 1 - s`; this is the symmetry coming
from the functional equation of the completed zeta function. -/
theorem nontrivialZeros_one_sub {s : ℂ} (hs : s ∈ nontrivialZeros) : 1 - s ∈ nontrivialZeros := by
  obtain ⟨hz, htriv, hone⟩ := hs
  have hs0 : s ≠ 0 := ne_zero_of_mem_nontrivialZeros ⟨hz, htriv, hone⟩
  have hGne : Gammaℝ s ≠ 0 := by
    rw [Ne, Gammaℝ_eq_zero_iff]
    rintro ⟨n, hn⟩
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · exact hs0 (by simpa using hn)
    · refine htriv ⟨n - 1, ?_⟩
      have hone' : ((n : ℂ) - 1 + 1) = n := by ring
      have hcast : ((n - 1 : ℕ) : ℂ) = (n : ℂ) - 1 := by
        have h1n : (1 : ℕ) ≤ n := hpos
        push_cast [Nat.cast_sub h1n]
        ring
      rw [hn, hcast, hone']
      ring
  have hLam : completedRiemannZeta s = 0 := by
    have h := riemannZeta_def_of_ne_zero hs0
    rw [hz] at h
    rcases div_eq_zero_iff.mp h.symm with h1 | h1
    · exact h1
    · exact absurd h1 hGne
  have hLam2 : completedRiemannZeta (1 - s) = 0 := by
    rw [completedRiemannZeta_one_sub]; exact hLam
  have h1s0 : (1 : ℂ) - s ≠ 0 := fun h => hone (by linear_combination -h)
  refine ⟨by rw [riemannZeta_def_of_ne_zero h1s0, hLam2, zero_div], ?_, ?_⟩
  · rintro ⟨n, hn⟩
    have hs' : s = 2 * n + 3 := by linear_combination -hn
    have hre : 1 < s.re := by
      rw [hs']
      simp only [Complex.add_re, Complex.mul_re, Complex.re_ofNat, Complex.natCast_re,
        Complex.im_ofNat, Complex.natCast_im, mul_zero, sub_zero]
      have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    exact riemannZeta_ne_zero_of_one_lt_re hre hz
  · exact fun h => hs0 (by linear_combination -h)

/-- For `s ≠ 0`, the point `1 - 1/s` lies in the closed unit disc iff `Re s ≥ 1/2`. -/
theorem norm_one_sub_inv_le_one_iff {s : ℂ} (hs : s ≠ 0) : ‖1 - 1 / s‖ ≤ 1 ↔ 1 / 2 ≤ s.re := by
  have h1 : 1 - 1 / s = (s - 1) / s := by field_simp
  rw [h1, norm_div, div_le_one (by positivity)]
  constructor
  · intro h
    have h2 : ‖s - 1‖ ^ 2 ≤ ‖s‖ ^ 2 := by nlinarith [norm_nonneg (s - 1), norm_nonneg s]
    rw [Complex.sq_norm, Complex.sq_norm] at h2
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.one_re, Complex.sub_im,
      Complex.one_im, sub_zero] at h2
    nlinarith
  · intro h
    have h2 : ‖s - 1‖ ^ 2 ≤ ‖s‖ ^ 2 := by
      rw [Complex.sq_norm, Complex.sq_norm]
      simp only [Complex.normSq_apply, Complex.sub_re, Complex.one_re, Complex.sub_im,
        Complex.one_im, sub_zero]
      nlinarith
    nlinarith [norm_nonneg (s - 1), norm_nonneg s]

/-- For `s ≠ 0`, the point `1 - 1/s` lies on the unit circle iff `Re s = 1/2`. -/
theorem norm_one_sub_inv_eq_one_iff {s : ℂ} (hs : s ≠ 0) : ‖1 - 1 / s‖ = 1 ↔ s.re = 1 / 2 := by
  have h1 : 1 - 1 / s = (s - 1) / s := by field_simp
  rw [h1, norm_div, div_eq_one_iff_eq (by positivity)]
  constructor
  · intro h
    have h2 : ‖s - 1‖ ^ 2 = ‖s‖ ^ 2 := by rw [h]
    rw [Complex.sq_norm, Complex.sq_norm] at h2
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.one_re, Complex.sub_im,
      Complex.one_im, sub_zero] at h2
    nlinarith
  · intro h
    have h2 : ‖s - 1‖ ^ 2 = ‖s‖ ^ 2 := by
      rw [Complex.sq_norm, Complex.sq_norm]
      simp only [Complex.normSq_apply, Complex.sub_re, Complex.one_re, Complex.sub_im,
        Complex.one_im, sub_zero]
      nlinarith
    nlinarith [norm_nonneg (s - 1), norm_nonneg s]

/-- **Li's coefficients**, expressed as a sum over the (enumerated) nontrivial zeros:
`λ n = ∑_ρ Re (1 - (1 - 1/ρ) ^ n)`. -/
noncomputable def liCoeff (ρ : ℕ → ℂ) (n : ℕ) : ℝ := liSumOf (fun k => 1 - 1 / ρ k) n

/-- **Li's criterion for the Riemann Hypothesis.**

Let `ρ : ℕ → ℂ` enumerate (possibly with multiplicities) the nontrivial zeros of the Riemann
zeta function: every `ρ k` is a nontrivial zero (`hmem`) and every nontrivial zero occurs in
the list (`honto`).  The two remaining hypotheses are the classical unconditional convergence
properties of the zeros, which are not currently available in Mathlib and are therefore
assumed here: absolute convergence of `∑_ρ Re (1/ρ)` (`hsum1`) and of
`∑_ρ (‖1 - 1/ρ‖ - 1)⁺` (`hsum2`).

Then the Riemann Hypothesis holds if and only if all Li coefficients
`λ n = ∑_ρ Re (1 - (1 - 1/ρ) ^ n)` are nonnegative for `n ≥ 1`.

The symmetry `ρ ↦ 1 - ρ` of the zero set is *proved* here (`nontrivialZeros_one_sub`) from the
functional equation of the completed zeta function, and the equivalence itself is proved in
full: the forward direction from `‖ 1 - 1/ρ ‖ = 1` on the critical line, the reverse direction
by the abstract positivity criterion `liSumOf_nonneg_iff`. -/
theorem RH_Li_criterion (ρ : ℕ → ℂ)
    (hmem : ∀ k, ρ k ∈ nontrivialZeros)
    (honto : ∀ s ∈ nontrivialZeros, ∃ k, ρ k = s)
    (hsum1 : Summable fun k => (1 / ρ k).re)
    (hsum2 : Summable fun k => max 0 (‖1 - 1 / ρ k‖ - 1)) :
    RiemannHypothesis ↔ ∀ n : ℕ, 1 ≤ n → 0 ≤ liCoeff ρ n := by
  have hzne : ∀ k, ρ k ≠ 0 := fun k => ne_zero_of_mem_nontrivialZeros (hmem k)
  have hd : Summable fun k => 1 - ((fun k => 1 - 1 / ρ k) k).re := by
    have hfun : (fun k => 1 - ((fun k => 1 - 1 / ρ k) k).re) = fun k => (1 / ρ k).re := by
      funext k; simp
    rw [hfun]; exact hsum1
  constructor
  · intro hRH n hn
    refine liSumOf_nonneg_of_norm_le_one (fun k => ?_) n
    have hk := (riemannHypothesis_iff.mp hRH) (ρ k) (hmem k)
    exact ((norm_one_sub_inv_eq_one_iff (hzne k)).mpr hk).le
  · intro hpos
    have hball : ∀ k, ‖1 - 1 / ρ k‖ ≤ 1 :=
      norm_le_one_of_liSumOf_nonneg hd hsum2 fun n hn => hpos n hn
    have hre : ∀ k, 1 / 2 ≤ (ρ k).re := fun k =>
      (norm_one_sub_inv_le_one_iff (hzne k)).mp (hball k)
    rw [riemannHypothesis_iff]
    intro s hs
    obtain ⟨k, rfl⟩ := honto s hs
    obtain ⟨k', hk'⟩ := honto _ (nontrivialZeros_one_sub (hmem k))
    have hk2 := hre k'
    rw [hk'] at hk2
    simp only [Complex.sub_re, Complex.one_re] at hk2
    linarith [hre k]

end Frontier

