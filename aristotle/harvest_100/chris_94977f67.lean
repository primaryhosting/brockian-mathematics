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
# Config Count Over Main Tendsto
Category: Brockian (Literature Discharge)
Target: Brockian.EquidistributionBVReduction.configCount_over_main_tendsto
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
The named hypothesis `configCount_over_main_tendsto` of the equidistribution /
Bombieri–Vinogradov reduction is discharged here: it is Mertens' classical asymptotic
`∑_{q ≤ N} φ(q) ∼ 3 N² / π²`.

The proof follows the standard argument.  Möbius inversion of `∑_{d ∣ n} φ(d) = n`
(`ArithmeticFunction.sum_eq_iff_sum_smul_moebius_eq` applied to `Nat.sum_totient`) gives the
hyperbola expansion `∑_{q ≤ N} φ(q) = ∑_{d ≤ N} μ(d) · T(⌊N/d⌋)` with `T(m) = m(m+1)/2`.
Comparing `T(⌊N/d⌋)/N²` with `1/(2d²)` termwise costs `O(1/(Nd))`, so the error is
`O(H_N / N) → 0`, while the truncated Möbius sum converges to
`∑_{d ≥ 1} μ(d)/d² = 1/ζ(2) = 6/π²`; the last identity is taken from Mathlib
(`ArithmeticFunction.LSeries_zeta_mul_Lseries_moebius`, `LSeries_zeta_eq_riemannZeta` and
`riemannZeta_two`).
-/

open ArithmeticFunction Finset Filter

namespace Brockian.EquidistributionBVReduction

/-- The number of *configurations* `(q, a)` with `1 ≤ q ≤ N`, `1 ≤ a ≤ q` and `gcd (a, q) = 1`;
these are the (modulus, primitive residue class) pairs available to an equidistribution /
Bombieri–Vinogradov style reduction with moduli up to `N`.  It equals `∑_{q ≤ N} φ(q)`. -/
noncomputable def configCount (N : ℕ) : ℝ := ∑ q ∈ Finset.Icc 1 N, (q.totient : ℝ)

/-- The main term for `configCount`, namely `3 N² / π² = N² / (2 ζ(2))`. -/
noncomputable def mainTerm (N : ℕ) : ℝ := 3 * (N : ℝ) ^ 2 / Real.pi ^ 2

/-- `∑_{d ≥ 1} μ(d) / d² = 1 / ζ(2) = 6 / π²`. -/
theorem moebius_div_sq_hasSum :
    HasSum (fun d : ℕ => (moebius d : ℝ) / (d : ℝ) ^ 2) (6 / Real.pi ^ 2) := by
  have hs : (1 : ℝ) < ((2 : ℂ)).re := by norm_num
  have hz : LSeries (fun n => (zeta n : ℂ)) 2 = riemannZeta 2 := LSeries_zeta_eq_riemannZeta hs
  have hprod := LSeries_zeta_mul_Lseries_moebius hs
  rw [hz, riemannZeta_two] at hprod
  have hmu : LSeries (fun n => (moebius n : ℂ)) 2 = 6 / (Real.pi : ℂ) ^ 2 := by
    have hpi : ((Real.pi : ℂ)) ≠ 0 := by
      simp [Real.pi_ne_zero]
    field_simp at hprod ⊢
    linear_combination hprod
  have hsum : LSeriesHasSum (fun n => (moebius n : ℂ)) 2 (6 / (Real.pi : ℂ) ^ 2) := by
    rw [← hmu]
    exact (LSeriesSummable_moebius_iff.mpr hs).hasSum
  rw [← Complex.hasSum_ofReal]
  have hfun : (fun d : ℕ => (((moebius d : ℝ) / (d : ℝ) ^ 2 : ℝ) : ℂ))
      = LSeries.term (fun n => (moebius n : ℂ)) 2 := by
    funext d
    rcases eq_or_ne d 0 with rfl | hd
    · simp [LSeries.term]
    · rw [LSeries.term_of_ne_zero hd]
      push_cast
      norm_num
  rw [hfun]
  push_cast
  exact hsum

/-- Möbius inversion of `∑_{d ∣ n} φ(d) = n`. -/
theorem totient_eq_sum_moebius (n : ℕ) (hn : 0 < n) :
    (n.totient : ℝ) = ∑ p ∈ n.divisorsAntidiagonal, (moebius p.1 : ℝ) * (p.2 : ℝ) := by
  have h := (ArithmeticFunction.sum_eq_iff_sum_smul_moebius_eq
      (f := fun n : ℕ => (n.totient : ℝ)) (g := fun n : ℕ => (n : ℝ))).mp
    (by
      intro m _
      exact_mod_cast congrArg (Nat.cast : ℕ → ℝ) (Nat.sum_totient m)) n hn
  rw [← h]
  exact Finset.sum_congr rfl fun p _ => by simp [zsmul_eq_mul]

/-- Interchanging the order of summation in `∑_{q ≤ N} ∑_{de = q}`. -/
theorem sum_divisorsAntidiagonal_swap (N : ℕ) (F : ℕ × ℕ → ℝ) :
    ∑ q ∈ Finset.Icc 1 N, ∑ p ∈ q.divisorsAntidiagonal, F p
      = ∑ d ∈ Finset.Icc 1 N, ∑ e ∈ Finset.Icc 1 (N / d), F (d, e) := by
  rw [Finset.sum_sigma', Finset.sum_sigma']
  refine Finset.sum_nbij' (i := fun x => (⟨x.2.1, x.2.2⟩ : (_ : ℕ) × ℕ))
    (j := fun y => (⟨y.1 * y.2, (y.1, y.2)⟩ : (_ : ℕ) × ℕ × ℕ)) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨q, d, e⟩ hx
    simp only [Finset.mem_sigma, Finset.mem_Icc, Nat.mem_divisorsAntidiagonal] at hx ⊢
    obtain ⟨⟨hq1, hqN⟩, hde, hq0⟩ := hx
    have hd0 : 0 < d := Nat.pos_of_ne_zero (by rintro rfl; simp at hde; omega)
    have he0 : 0 < e := Nat.pos_of_ne_zero (by rintro rfl; simp at hde; omega)
    refine ⟨⟨hd0, ?_⟩, he0, ?_⟩
    · calc d ≤ d * e := Nat.le_mul_of_pos_right _ he0
        _ = q := hde
        _ ≤ N := hqN
    · rw [Nat.le_div_iff_mul_le hd0, mul_comm]; omega
  · rintro ⟨d, e⟩ hy
    simp only [Finset.mem_sigma, Finset.mem_Icc, Nat.mem_divisorsAntidiagonal] at hy ⊢
    obtain ⟨⟨hd1, hdN⟩, he1, heN⟩ := hy
    rw [Nat.le_div_iff_mul_le hd1, mul_comm] at heN
    exact ⟨⟨by nlinarith, heN⟩, trivial, by positivity⟩
  · rintro ⟨q, d, e⟩ hx
    simp only [Finset.mem_sigma, Nat.mem_divisorsAntidiagonal] at hx
    simp [hx.2.1]
  · rintro ⟨d, e⟩ _
    rfl
  · rintro ⟨q, d, e⟩ _
    rfl

/-- Gauss' summation formula. -/
theorem sum_Icc_cast (m : ℕ) : ∑ e ∈ Finset.Icc 1 m, (e : ℝ) = m * (m + 1) / 2 := by
  induction m with
  | zero => simp
  | succ k ih => rw [Finset.sum_Icc_succ_top (by omega), ih]; push_cast; ring

/-- The hyperbola-method expansion `∑_{q ≤ N} φ(q) = ∑_{d ≤ N} μ(d) · T(⌊N/d⌋)`. -/
theorem configCount_eq (N : ℕ) :
    configCount N
      = ∑ d ∈ Finset.Icc 1 N,
          (moebius d : ℝ) * (((N / d : ℕ) : ℝ) * (((N / d : ℕ) : ℝ) + 1) / 2) := by
  rw [configCount, Finset.sum_congr rfl (fun q hq => totient_eq_sum_moebius q
    (by simpa using (Finset.mem_Icc.mp hq).1))]
  rw [sum_divisorsAntidiagonal_swap N (fun p => (moebius p.1 : ℝ) * (p.2 : ℝ))]
  refine Finset.sum_congr rfl fun d _ => ?_
  simp only []
  rw [← Finset.mul_sum, sum_Icc_cast]

/-- Termwise comparison of `T(⌊N/d⌋)/N²` with `1/(2d²)`. -/
theorem triangle_approx {N d : ℕ} (hd : 1 ≤ d) (hdN : d ≤ N) :
    |((N / d : ℕ) : ℝ) * (((N / d : ℕ) : ℝ) + 1) / 2 / (N : ℝ) ^ 2 - 1 / (2 * (d : ℝ) ^ 2)|
      ≤ 2 / ((N : ℝ) * d) := by
  have hdivmod := Nat.div_add_mod N d
  have hmod : N % d < d := Nat.mod_lt _ (by omega)
  have h1 : (N / d) * d ≤ N := Nat.div_mul_le_self N d
  have h2 : N < (N / d + 1) * d := by
    have h3 : (N / d + 1) * d = d * (N / d) + d := by ring
    omega
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hm0 : (0 : ℝ) ≤ ((N / d : ℕ) : ℝ) := Nat.cast_nonneg _
  have hA : ((N / d : ℕ) : ℝ) * d ≤ (N : ℝ) := by exact_mod_cast h1
  have hB : (N : ℝ) < (((N / d : ℕ) : ℝ) + 1) * d := by exact_mod_cast h2
  have key : ((N / d : ℕ) : ℝ) * (((N / d : ℕ) : ℝ) + 1) / 2 / (N : ℝ) ^ 2 - 1 / (2 * (d : ℝ) ^ 2)
      = ((d : ℝ) ^ 2 * ((N / d : ℕ) : ℝ) * (((N / d : ℕ) : ℝ) + 1) - (N : ℝ) ^ 2)
        / (2 * (N : ℝ) ^ 2 * (d : ℝ) ^ 2) := by
    field_simp
  have hrhs : 2 / ((N : ℝ) * d) * (2 * (N : ℝ) ^ 2 * (d : ℝ) ^ 2) = 4 * N * d := by
    field_simp; ring
  rw [key, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * (N : ℝ) ^ 2 * (d : ℝ) ^ 2),
    div_le_iff₀ (by positivity), hrhs, abs_le]
  constructor
  · nlinarith [sq_nonneg ((N : ℝ) - ((N / d : ℕ) : ℝ) * d), mul_pos hN0 hd0,
      mul_nonneg hm0 hd0.le]
  · nlinarith [sq_nonneg ((N : ℝ) - ((N / d : ℕ) : ℝ) * d), mul_pos hN0 hd0,
      mul_nonneg hm0 hd0.le]

/-- The truncated Möbius sum `∑_{d ≤ N} μ(d)/d²`. -/
noncomputable def moebiusPartial (N : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 N, (moebius d : ℝ) / (d : ℝ) ^ 2

/-- The harmonic sum `∑_{d ≤ N} 1/d`. -/
noncomputable def harm (N : ℕ) : ℝ := ∑ d ∈ Finset.Icc 1 N, (1 : ℝ) / d

theorem sum_range_succ_eq_sum_Icc (N : ℕ) (f : ℕ → ℝ) (hf : f 0 = 0) :
    ∑ i ∈ Finset.range (N + 1), f i = ∑ i ∈ Finset.Icc 1 N, f i := by
  rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range, Finset.sum_range_succ' f N]
  simp [hf, add_comm]

theorem moebiusPartial_tendsto :
    Tendsto moebiusPartial atTop (nhds (6 / Real.pi ^ 2)) := by
  have h2 : Tendsto (fun N : ℕ => ∑ i ∈ Finset.range (N + 1), (moebius i : ℝ) / (i : ℝ) ^ 2) atTop
      (nhds (6 / Real.pi ^ 2)) :=
    moebius_div_sq_hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
  exact h2.congr fun N => sum_range_succ_eq_sum_Icc N _ (by simp)

theorem harm_div_tendsto : Tendsto (fun N : ℕ => harm N / N) atTop (nhds 0) := by
  have hu : Tendsto (fun i : ℕ => 1 / ((i : ℝ) + 1)) atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  refine hu.cesaro.congr fun N => ?_
  rw [harm, ← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range, div_eq_inv_mul]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  push_cast
  ring_nf

theorem abs_moebius_le_one (d : ℕ) : |(moebius d : ℝ)| ≤ 1 := by
  by_cases h : Squarefree d
  · rw [ArithmeticFunction.moebius_apply_of_squarefree h]
    push_cast
    rw [abs_pow]
    simp
  · simp [ArithmeticFunction.moebius_eq_zero_of_not_squarefree h]

/-- The error in replacing `configCount N / N²` by half the truncated Möbius sum. -/
theorem configCount_error_bound (N : ℕ) :
    |configCount N / (N : ℝ) ^ 2 - moebiusPartial N / 2| ≤ 2 * (harm N / N) := by
  have hdiff : configCount N / (N : ℝ) ^ 2 - moebiusPartial N / 2
      = ∑ d ∈ Finset.Icc 1 N, (moebius d : ℝ) *
          (((N / d : ℕ) : ℝ) * (((N / d : ℕ) : ℝ) + 1) / 2 / (N : ℝ) ^ 2
            - 1 / (2 * (d : ℝ) ^ 2)) := by
    rw [configCount_eq, moebiusPartial, Finset.sum_div, Finset.sum_div, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun d _ => by ring
  rw [hdiff]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hbound : ∀ d ∈ Finset.Icc 1 N,
      |(moebius d : ℝ) * (((N / d : ℕ) : ℝ) * (((N / d : ℕ) : ℝ) + 1) / 2 / (N : ℝ) ^ 2
        - 1 / (2 * (d : ℝ) ^ 2))| ≤ 2 / ((N : ℝ) * d) := by
    intro d hd
    obtain ⟨hd1, hdN⟩ := Finset.mem_Icc.mp hd
    rw [abs_mul]
    exact le_trans (mul_le_of_le_one_left (abs_nonneg _) (abs_moebius_le_one d))
      (triangle_approx hd1 hdN)
  refine (Finset.sum_le_sum hbound).trans ?_
  rw [harm, Finset.sum_div, Finset.mul_sum]
  exact Finset.sum_le_sum fun d _ => le_of_eq (by ring)

theorem configCount_div_sq_tendsto :
    Tendsto (fun N : ℕ => configCount N / (N : ℝ) ^ 2) atTop (nhds (3 / Real.pi ^ 2)) := by
  have hzero : Tendsto (fun N : ℕ => configCount N / (N : ℝ) ^ 2 - moebiusPartial N / 2) atTop
      (nhds 0) := by
    refine squeeze_zero_norm (fun N => ?_) (by simpa using harm_div_tendsto.const_mul 2)
    simpa [Real.norm_eq_abs] using configCount_error_bound N
  have h := hzero.add (moebiusPartial_tendsto.div_const 2)
  have hval : (0 : ℝ) + (6 / Real.pi ^ 2) / 2 = 3 / Real.pi ^ 2 := by ring
  rw [hval] at h
  exact h.congr fun N => by ring

/-- **Mertens' theorem** in the form required by the equidistribution / Bombieri–Vinogradov
reduction: the configuration count `∑_{q ≤ N} φ(q)` is asymptotic to its main term `3 N² / π²`. -/
theorem configCount_over_main_tendsto :
    Tendsto (fun N : ℕ => configCount N / mainTerm N) atTop (nhds 1) := by
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have h := configCount_div_sq_tendsto.mul_const (Real.pi ^ 2 / 3)
  have hlim : 3 / Real.pi ^ 2 * (Real.pi ^ 2 / 3) = 1 := by field_simp
  rw [hlim] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with N hN
  have hN0 : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [mainTerm]
  field_simp

end Brockian.EquidistributionBVReduction

