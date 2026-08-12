import Mathlib
import RequestProject.Brun.Final

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

/-- **Brun's theorem**: the sum of the reciprocals of the twin primes converges.

The twin primes are indexed by the subtype of naturals `p` such that both `p` and `p + 2`
are prime, and the summand is `1 / p`. -/
theorem Frontier.Brun_twin_reciprocal :
    Summable (fun p : {p : ℕ // Nat.Prime p ∧ Nat.Prime (p + 2)} => (1 : ℝ) / (p.1 : ℝ)) := by
  have h : Summable (Brun.twinIndicator ∘
      (Subtype.val : {p : ℕ // Nat.Prime p ∧ Nat.Prime (p + 2)} → ℕ)) :=
    Brun.summable_twinIndicator'.comp_injective Subtype.val_injective
  refine h.congr (fun p => ?_)
  simp only [Function.comp_apply, Brun.twinIndicator, if_pos p.2]

import RequestProject.Brun.Defs

/-!
# Dyadic decomposition

Summability of `∑ 1/p` over twin primes follows from summability of
`m ↦ twinCount (2^m) / 2^m`.
-/

namespace Brun

open Finset

/-- `1/n` if `n, n+2` are both prime, and `0` otherwise. -/
noncomputable def twinIndicator (n : ℕ) : ℝ :=
  if Nat.Prime n ∧ Nat.Prime (n + 2) then 1 / n else 0

lemma twinIndicator_nonneg (n : ℕ) : 0 ≤ twinIndicator n := by
  unfold twinIndicator
  split
  · positivity
  · exact le_rfl

lemma sum_Ico_twinIndicator_le (M : ℕ) :
    ∑ n ∈ Ico (2 ^ M) (2 ^ (M + 1)), twinIndicator n
      ≤ (twinCount (2 ^ (M + 1)) : ℝ) / 2 ^ M := by
  have h1 : ∑ n ∈ Ico (2 ^ M) (2 ^ (M + 1)), twinIndicator n
      ≤ ∑ n ∈ Ico (2 ^ M) (2 ^ (M + 1)),
          (if Nat.Prime n ∧ Nat.Prime (n + 2) then (1 : ℝ) / 2 ^ M else 0) := by
    refine Finset.sum_le_sum (fun n hn => ?_)
    simp only [Finset.mem_Ico] at hn
    unfold twinIndicator
    split
    · apply one_div_le_one_div_of_le (by positivity)
      exact_mod_cast hn.1
    · exact le_rfl
  have h2 : ∑ n ∈ Ico (2 ^ M) (2 ^ (M + 1)),
      (if Nat.Prime n ∧ Nat.Prime (n + 2) then (1 : ℝ) / 2 ^ M else 0)
      = (((Ico (2 ^ M) (2 ^ (M + 1))).filter
          (fun n => Nat.Prime n ∧ Nat.Prime (n + 2))).card : ℝ) / 2 ^ M := by
    rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const]
    simp [nsmul_eq_mul, div_eq_mul_inv]
  have h3 : ((Ico (2 ^ M) (2 ^ (M + 1))).filter
      (fun n => Nat.Prime n ∧ Nat.Prime (n + 2))).card ≤ twinCount (2 ^ (M + 1)) := by
    rw [twinCount]
    refine Finset.card_le_card (fun n hn => ?_)
    simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_range] at hn ⊢
    exact ⟨hn.1.2, hn.2⟩
  have h4 : (((Ico (2 ^ M) (2 ^ (M + 1))).filter
      (fun n => Nat.Prime n ∧ Nat.Prime (n + 2))).card : ℝ) ≤ (twinCount (2 ^ (M + 1)) : ℝ) := by
    exact_mod_cast h3
  calc ∑ n ∈ Ico (2 ^ M) (2 ^ (M + 1)), twinIndicator n ≤ _ := h1
    _ = _ := h2
    _ ≤ (twinCount (2 ^ (M + 1)) : ℝ) / 2 ^ M := by gcongr

lemma sum_range_two_pow_twinIndicator_le (M : ℕ) :
    ∑ n ∈ range (2 ^ M), twinIndicator n
      ≤ ∑ m ∈ range M, (twinCount (2 ^ (m + 1)) : ℝ) / 2 ^ m := by
  induction M with
  | zero => simp [twinIndicator]
  | succ M ih =>
      have hsplit : ∑ n ∈ range (2 ^ (M + 1)), twinIndicator n
          = ∑ n ∈ range (2 ^ M), twinIndicator n
            + ∑ n ∈ Ico (2 ^ M) (2 ^ (M + 1)), twinIndicator n := by
        rw [Finset.range_eq_Ico,
          ← Finset.sum_Ico_consecutive _ (Nat.zero_le (2 ^ M))
            (Nat.pow_le_pow_right (by norm_num) (by omega) : 2 ^ M ≤ 2 ^ (M + 1))]
      rw [hsplit, Finset.sum_range_succ]
      have := sum_Ico_twinIndicator_le M
      linarith

/-- Summability of the twin prime indicator series, given the dyadic bound. -/
theorem summable_twinIndicator
    (h : Summable (fun m : ℕ => (twinCount (2 ^ (m + 1)) : ℝ) / 2 ^ m)) :
    Summable twinIndicator := by
  have hnn : ∀ m : ℕ, 0 ≤ (twinCount (2 ^ (m + 1)) : ℝ) / 2 ^ m := by
    intro m; positivity
  refine summable_of_sum_range_le twinIndicator_nonneg (c := ∑' m, (twinCount (2 ^ (m + 1)) : ℝ) / 2 ^ m) ?_
  intro K
  have hK : K ≤ 2 ^ K := Nat.le_of_lt (Nat.lt_two_pow_self)
  have h1 : ∑ n ∈ range K, twinIndicator n ≤ ∑ n ∈ range (2 ^ K), twinIndicator n := by
    refine Finset.sum_le_sum_of_subset_of_nonneg
      (fun x hx => Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hx) hK)) ?_
    intro n _ _
    exact twinIndicator_nonneg n
  have h2 := sum_range_two_pow_twinIndicator_le K
  have h3 : ∑ m ∈ range K, (twinCount (2 ^ (m + 1)) : ℝ) / 2 ^ m
      ≤ ∑' m, (twinCount (2 ^ (m + 1)) : ℝ) / 2 ^ m :=
    Summable.sum_le_tsum _ (fun i _ => hnn i) h
  linarith

end Brun

import RequestProject.Brun.Sieve

/-!
# Choosing the sieve parameters

With `N = 2^m`, sieve level `z = 2^q` and truncation level `k = 20 ℓ` where `ℓ = log₂ m` and
`q = m / (40 ℓ)`, Brun's sieve bound gives
`twinCount (2^m) / 2^m = O(√m / m²)`, which is summable.
-/

set_option maxHeartbeats 2000000

namespace Brun

open Finset Filter

/-! ### Elementary growth lemmas -/

lemma poly_le_geom (A : ℕ) : ∃ C : ℝ, 0 < C ∧ ∀ t : ℕ, (t : ℝ) ^ A ≤ C * 2 ^ t := by
  have h : Tendsto (fun n : ℕ => (n : ℝ) ^ A * (1 / 2 : ℝ) ^ n) atTop (nhds 0) :=
    tendsto_pow_const_mul_const_pow_of_abs_lt_one A (by norm_num)
  obtain ⟨C, hC⟩ := h.bddAbove_range
  refine ⟨max C 1, by positivity, fun t => ?_⟩
  have ht : (t : ℝ) ^ A * (1 / 2 : ℝ) ^ t ≤ C := hC ⟨t, rfl⟩
  have hpow : ((1 : ℝ) / 2) ^ t * 2 ^ t = 1 := by rw [← mul_pow]; norm_num
  have hrw : (t : ℝ) ^ A = ((t : ℝ) ^ A * (1 / 2 : ℝ) ^ t) * 2 ^ t := by
    rw [mul_assoc, hpow, mul_one]
  rw [hrw]
  exact mul_le_mul_of_nonneg_right (le_trans ht (le_max_left _ _)) (by positivity)

lemma poly_div_two_pow_half_le (A : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 2 ≤ m → (m : ℝ) ^ A / 2 ^ (m / 2) ≤ C / (m : ℝ) ^ 2 := by
  obtain ⟨C, hCpos, hC⟩ := poly_le_geom (A + 2)
  refine ⟨3 ^ (A + 2) * C, by positivity, fun m hm => ?_⟩
  set t := m / 2 with ht
  have ht1 : 1 ≤ t := by omega
  have hmt : m ≤ 3 * t := by omega
  have hmR : (0 : ℝ) < (m : ℝ) := by
    have : 0 < m := by omega
    exact_mod_cast this
  have h1 : (m : ℝ) ^ (A + 2) ≤ (3 * t : ℝ) ^ (A + 2) := by
    apply pow_le_pow_left₀ (le_of_lt hmR)
    exact_mod_cast hmt
  have h2 : (3 * t : ℝ) ^ (A + 2) = 3 ^ (A + 2) * (t : ℝ) ^ (A + 2) := by rw [mul_pow]
  have h3 : (m : ℝ) ^ (A + 2) ≤ 3 ^ (A + 2) * C * 2 ^ t := by
    have := hC t
    nlinarith [pow_pos (show (0:ℝ) < 3 by norm_num) (A + 2)]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  calc (m : ℝ) ^ A * (m : ℝ) ^ 2 = (m : ℝ) ^ (A + 2) := by rw [← pow_add]
    _ ≤ 3 ^ (A + 2) * C * 2 ^ t := h3

lemma log_sq_le : ∃ C : ℝ, 0 < C ∧
    ∀ m : ℕ, 1 ≤ m → ((Nat.log 2 m : ℝ)) ^ 2 ≤ C * Real.sqrt m := by
  obtain ⟨C, hCpos, hC⟩ := poly_le_geom 4
  refine ⟨Real.sqrt C, Real.sqrt_pos.mpr hCpos, fun m hm => ?_⟩
  set l := Nat.log 2 m with hl
  have h1 : (2 : ℕ) ^ l ≤ m := Nat.pow_log_le_self 2 (by omega)
  have h2 : ((2 : ℝ)) ^ l ≤ (m : ℝ) := by exact_mod_cast h1
  have h3 : (l : ℝ) ^ 4 ≤ C * (m : ℝ) := by
    have := hC l
    nlinarith [hCpos, h2]
  have h4 : Real.sqrt ((l : ℝ) ^ 4) ≤ Real.sqrt (C * m) := Real.sqrt_le_sqrt h3
  rw [show ((l : ℝ) ^ 4) = ((l : ℝ) ^ 2) ^ 2 by ring, Real.sqrt_sq (by positivity),
    Real.sqrt_mul hCpos.le] at h4
  exact h4

lemma summable_sqrt_div_sq : Summable (fun m : ℕ => Real.sqrt m / (m : ℝ) ^ 2) := by
  have h : ∀ m : ℕ, Real.sqrt m / (m : ℝ) ^ 2 = 1 / (m : ℝ) ^ ((3 : ℝ) / 2) := by
    intro m
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp
    · have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
      have h2 : ((m : ℝ) ^ (2 : ℕ)) = (m : ℝ) ^ ((2 : ℝ)) := by
        rw [← Real.rpow_natCast (m : ℝ) 2]; norm_num
      rw [Real.sqrt_eq_rpow, h2, ← Real.rpow_sub hm0,
        show (1 : ℝ) / 2 - 2 = -((3 : ℝ) / 2) by ring, Real.rpow_neg hm0.le]
      simp
  simp only [h]
  rw [Real.summable_one_div_nat_rpow]
  norm_num

lemma eighty_mul_le_two_pow {l : ℕ} (hl : 10 ≤ l) : 80 * l ≤ 2 ^ l := by
  induction l with
  | zero => omega
  | succ l ih =>
      rcases Nat.lt_or_ge l 10 with h | h
      · have hl9 : l = 9 := by omega
        subst hl9
        norm_num
      · have hih := ih h
        have h2 : (80 : ℕ) ≤ 2 ^ l := by
          calc (80 : ℕ) ≤ 2 ^ 7 := by norm_num
            _ ≤ 2 ^ l := Nat.pow_le_pow_right (by norm_num) (by omega)
        calc 80 * (l + 1) = 80 * l + 80 := by ring
          _ ≤ 2 ^ l + 2 ^ l := by omega
          _ = 2 ^ (l + 1) := by ring

lemma two_pow_div_le {a b c : ℕ} (h : a + c ≤ b) : (2 : ℝ) ^ a / 2 ^ b ≤ 1 / 2 ^ c := by
  rw [div_le_div_iff₀ (by positivity) (by positivity), one_mul, ← pow_add]
  exact pow_le_pow_right₀ one_le_two h

/-! ### The parameter choice -/

lemma two_pow_mul_le {a b c : ℕ} (h : a + b ≤ c) : (2 : ℝ) ^ a * 2 ^ b ≤ 2 ^ c := by
  rw [← pow_add]
  exact pow_le_pow_right₀ one_le_two h

/-- Brun's sieve bound with sieve level `z = 2 ^ q` and truncation level `k = 20 * l`, for
parameters `l`, `q` satisfying the required inequalities. -/
lemma twinCount_two_pow_bound_gen {m l q : ℕ} (hm : 1024 ≤ m) (hl10 : 10 ≤ l)
    (hpowl : 2 ^ l ≤ m) (hpowl2 : m < 2 * 2 ^ l) (hq2 : 2 ≤ q)
    (hqm : 40 * l * q ≤ m) (hqup : m < (q + 1) * (40 * l)) :
    (twinCount (2 ^ m) : ℝ) / 2 ^ m
      ≤ 2 / 2 ^ (m / 2) + 416000 * (l : ℝ) ^ 2 / (m : ℝ) ^ 2
        + Real.exp 20 * 2 ^ 19 / (m : ℝ) ^ 4 + 21 * (m : ℝ) ^ 41 / 2 ^ (m / 2) := by
  have hlpos : 0 < l := by omega
  have hlm : l ≤ m := le_trans (Nat.le_of_lt Nat.lt_two_pow_self) hpowl
  have hqm' : q ≤ m := le_trans (Nat.le_mul_of_pos_left q (by omega)) hqm
  have hq20 : 20 * l * q * 2 ≤ m := by
    calc 20 * l * q * 2 = 40 * l * q := by ring
      _ ≤ m := hqm
  have hq20' : 20 * l * q ≤ m / 2 := (Nat.le_div_iff_mul_le (by norm_num)).mpr hq20
  have hqhalf : q ≤ m / 2 := le_trans (Nat.le_mul_of_pos_left q (by omega)) hq20'
  have hm80 : m ≤ 80 * l * q := by
    have h1 : 40 * l ≤ 40 * l * q := Nat.le_mul_of_pos_right (40 * l) (by omega)
    calc m ≤ (q + 1) * (40 * l) := Nat.le_of_lt hqup
      _ = 40 * l * q + 40 * l := by ring
      _ ≤ 40 * l * q + 40 * l * q := Nat.add_le_add_left h1 _
      _ = 80 * l * q := by ring
  have hmpos : (0 : ℝ) < (m : ℝ) := by
    have : 0 < m := by omega
    exact_mod_cast this
  have hlR : (0 : ℝ) < (l : ℝ) := by exact_mod_cast hlpos
  have hqR : (0 : ℝ) < (q : ℝ) := by
    have : 0 < q := by omega
    exact_mod_cast this
  have hcast2q : ((2 ^ q : ℕ) : ℝ) = (2 : ℝ) ^ q := by push_cast; ring
  -- the dyadic quantity `D = 2^m / 2^(m/2)`
  have hD1 : (2 : ℝ) ^ q ≤ (2 : ℝ) ^ m / 2 ^ (m / 2) := by
    rw [le_div_iff₀ (by positivity)]
    exact two_pow_mul_le (by omega)
  have hD2 : (2 : ℝ) ^ (20 * l * q) ≤ (2 : ℝ) ^ m / 2 ^ (m / 2) := by
    rw [le_div_iff₀ (by positivity)]
    refine two_pow_mul_le ?_
    have h1 := hq20'
    generalize 20 * l * q = t at h1 ⊢
    omega
  -- bound on the main sieve product
  have hA : (∏ p ∈ oddPrimesLe (2 ^ q), (1 - 2 / (p : ℝ)))
      ≤ 416000 * (l : ℝ) ^ 2 / (m : ℝ) ^ 2 := by
    have h3 : 3 ≤ 2 ^ q := by
      calc (3 : ℕ) ≤ 2 ^ 2 := by norm_num
        _ ≤ 2 ^ q := Nat.pow_le_pow_right (by norm_num) hq2
    have hstep := prod_oddPrimesLe_one_sub_two_div_le h3
    have hlog : Real.log ((2 ^ q : ℕ) : ℝ) = (q : ℝ) * Real.log 2 := by
      rw [hcast2q, Real.log_pow]
    rw [hlog] at hstep
    have hlog2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
    have hexp : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
    have hexppos : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
    have hsq : (0.4804 : ℝ) ≤ (Real.log 2) ^ 2 := by nlinarith
    have hexp2 : Real.exp 1 ^ 2 ≤ 7.39 := by nlinarith
    have hq2sq : (0 : ℝ) < (q : ℝ) ^ 2 := by positivity
    have h65 : 4 * Real.exp 1 ^ 2 / ((q : ℝ) * Real.log 2) ^ 2 ≤ 65 / (q : ℝ) ^ 2 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [mul_nonneg (sub_nonneg.mpr hsq) hq2sq.le,
        mul_nonneg (sub_nonneg.mpr hexp2) hq2sq.le]
    have hA65 : (∏ p ∈ oddPrimesLe (2 ^ q), (1 - 2 / (p : ℝ))) ≤ 65 / (q : ℝ) ^ 2 :=
      le_trans hstep h65
    have hm80R : (m : ℝ) ≤ 80 * (l : ℝ) * (q : ℝ) := by exact_mod_cast hm80
    have hfinal : 65 / (q : ℝ) ^ 2 ≤ 416000 * (l : ℝ) ^ 2 / (m : ℝ) ^ 2 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [mul_self_le_mul_self hmpos.le hm80R, mul_pos hlR hqR]
    linarith
  -- bound on the error product
  have hB : (∏ p ∈ oddPrimesLe (2 ^ q), (1 + 4 / (p : ℝ))) / 2 ^ (20 * l + 1)
      ≤ Real.exp 20 * 2 ^ 19 / (m : ℝ) ^ 4 := by
    have hstep := prod_oddPrimesLe_one_add_four_div_le (q := q) (by omega)
    have hqle : (q : ℝ) ≤ (m : ℝ) := by exact_mod_cast hqm'
    have hBle : (∏ p ∈ oddPrimesLe (2 ^ q), (1 + 4 / (p : ℝ))) ≤ Real.exp 20 * (m : ℝ) ^ 16 := by
      refine le_trans hstep ?_
      have h16 : (q : ℝ) ^ 16 ≤ (m : ℝ) ^ 16 := pow_le_pow_left₀ hqR.le hqle 16
      nlinarith [Real.exp_pos 20]
    have hden : (m : ℝ) ^ 20 ≤ 2 ^ 20 * (2 : ℝ) ^ (20 * l) := by
      have h1 : (m : ℝ) ≤ 2 * (2 : ℝ) ^ l := by
        have h' : (m : ℝ) < ((2 * 2 ^ l : ℕ) : ℝ) := by exact_mod_cast hpowl2
        push_cast at h'
        linarith
      have h2 : (m : ℝ) ^ 20 ≤ (2 * (2 : ℝ) ^ l) ^ 20 := pow_le_pow_left₀ hmpos.le h1 20
      have h3 : (2 * (2 : ℝ) ^ l) ^ 20 = 2 ^ 20 * (2 : ℝ) ^ (20 * l) := by
        rw [mul_pow, ← pow_mul]
        ring_nf
      linarith [h3 ▸ h2]
    have hBnn : (0 : ℝ) ≤ ∏ p ∈ oddPrimesLe (2 ^ q), (1 + 4 / (p : ℝ)) := by
      refine Finset.prod_nonneg (fun p hp => ?_)
      have : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast oddPrimesLe_three_le hp
      positivity
    rw [pow_succ, div_le_div_iff₀ (by positivity) (by positivity)]
    have e1 : (∏ p ∈ oddPrimesLe (2 ^ q), (1 + 4 / (p : ℝ))) * (m : ℝ) ^ 4
        ≤ Real.exp 20 * (m : ℝ) ^ 16 * (m : ℝ) ^ 4 :=
      mul_le_mul_of_nonneg_right hBle (by positivity)
    have e2 : Real.exp 20 * (m : ℝ) ^ 16 * (m : ℝ) ^ 4 = Real.exp 20 * (m : ℝ) ^ 20 := by ring
    have e3 : Real.exp 20 * (m : ℝ) ^ 20 ≤ Real.exp 20 * (2 ^ 20 * (2 : ℝ) ^ (20 * l)) :=
      mul_le_mul_of_nonneg_left hden (Real.exp_pos 20).le
    have e4 : Real.exp 20 * (2 ^ 20 * (2 : ℝ) ^ (20 * l))
        = Real.exp 20 * 2 ^ 19 * ((2 : ℝ) ^ (20 * l) * 2) := by ring
    linarith
  -- the two error terms
  have hE1 : ((2 ^ q : ℕ) : ℝ) + 1 ≤ 2 * ((2 : ℝ) ^ m / 2 ^ (m / 2)) := by
    rw [hcast2q]
    have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ q := one_le_pow₀ (by norm_num)
    linarith
  have hE4 : (((20 * l : ℕ) : ℝ) + 1) * (2 * ((2 ^ q : ℕ) : ℝ) + 3) ^ (20 * l)
      ≤ 21 * (m : ℝ) ^ 41 * ((2 : ℝ) ^ m / 2 ^ (m / 2)) := by
    rw [hcast2q]
    have hq4 : (4 : ℝ) ≤ (2 : ℝ) ^ q := by
      have h : (2 : ℝ) ^ 2 ≤ (2 : ℝ) ^ q := pow_le_pow_right₀ (by norm_num) hq2
      norm_num at h
      linarith
    have hbase : 2 * (2 : ℝ) ^ q + 3 ≤ (2 : ℝ) ^ (q + 2) := by
      have hrw : (2 : ℝ) ^ (q + 2) = 4 * (2 : ℝ) ^ q := by rw [pow_add]; ring
      rw [hrw]
      linarith
    have hpow : (2 * (2 : ℝ) ^ q + 3) ^ (20 * l) ≤ ((2 : ℝ) ^ (q + 2)) ^ (20 * l) :=
      pow_le_pow_left₀ (by positivity) hbase _
    have hexpand : ((2 : ℝ) ^ (q + 2)) ^ (20 * l) = (2 : ℝ) ^ (20 * l * q) * (2 : ℝ) ^ (40 * l) := by
      rw [← pow_mul, ← pow_add]
      congr 1
      ring
    have h40 : (2 : ℝ) ^ (40 * l) ≤ (m : ℝ) ^ 40 := by
      have h1 : ((2 : ℝ) ^ l) ≤ (m : ℝ) := by exact_mod_cast hpowl
      calc (2 : ℝ) ^ (40 * l) = ((2 : ℝ) ^ l) ^ 40 := by rw [← pow_mul]; ring_nf
        _ ≤ (m : ℝ) ^ 40 := pow_le_pow_left₀ (by positivity) h1 40
    have hcoef : ((20 * l : ℕ) : ℝ) + 1 ≤ 21 * (m : ℝ) := by
      have hlmR : (l : ℝ) ≤ (m : ℝ) := by exact_mod_cast hlm
      have h1024 : (1024 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
      push_cast
      linarith
    have hstep1 : (2 * (2 : ℝ) ^ q + 3) ^ (20 * l) ≤ (2 : ℝ) ^ (20 * l * q) * (m : ℝ) ^ 40 := by
      rw [hexpand] at hpow
      nlinarith [pow_pos (show (0 : ℝ) < 2 by norm_num) (20 * l * q)]
    have hnn : (0 : ℝ) ≤ (2 * (2 : ℝ) ^ q + 3) ^ (20 * l) := by positivity
    have hmain : (((20 * l : ℕ) : ℝ) + 1) * (2 * (2 : ℝ) ^ q + 3) ^ (20 * l)
        ≤ (21 * (m : ℝ)) * ((2 : ℝ) ^ (20 * l * q) * (m : ℝ) ^ 40) :=
      mul_le_mul hcoef hstep1 hnn (by positivity)
    refine le_trans hmain ?_
    have hfac : (21 * (m : ℝ)) * ((2 : ℝ) ^ (20 * l * q) * (m : ℝ) ^ 40)
        = (21 * (m : ℝ) ^ 41) * (2 : ℝ) ^ (20 * l * q) := by ring
    rw [hfac]
    have hfin := mul_le_mul_of_nonneg_left hD2 (show (0 : ℝ) ≤ 21 * (m : ℝ) ^ 41 by positivity)
    calc (21 * (m : ℝ) ^ 41) * (2 : ℝ) ^ (20 * l * q)
        ≤ (21 * (m : ℝ) ^ 41) * ((2 : ℝ) ^ m / 2 ^ (m / 2)) := hfin
      _ = 21 * (m : ℝ) ^ 41 * ((2 : ℝ) ^ m / 2 ^ (m / 2)) := by ring
  -- assemble
  have hsieve := twinCount_le (2 ^ m) (2 ^ q) (20 * l) ⟨10 * l, by ring⟩
  have hNcast : ((2 ^ m : ℕ) : ℝ) = (2 : ℝ) ^ m := by push_cast; ring
  rw [hNcast] at hsieve
  rw [div_le_iff₀ (show (0 : ℝ) < (2 : ℝ) ^ m by positivity)]
  have hA' : (2 : ℝ) ^ m * (∏ p ∈ oddPrimesLe (2 ^ q), (1 - 2 / (p : ℝ)))
      ≤ (2 : ℝ) ^ m * (416000 * (l : ℝ) ^ 2 / (m : ℝ) ^ 2) :=
    mul_le_mul_of_nonneg_left hA (by positivity)
  have hB' : (2 : ℝ) ^ m * (∏ p ∈ oddPrimesLe (2 ^ q), (1 + 4 / (p : ℝ))) / 2 ^ (20 * l + 1)
      ≤ (2 : ℝ) ^ m * (Real.exp 20 * 2 ^ 19 / (m : ℝ) ^ 4) := by
    have h := mul_le_mul_of_nonneg_left hB (show (0 : ℝ) ≤ (2 : ℝ) ^ m by positivity)
    calc (2 : ℝ) ^ m * (∏ p ∈ oddPrimesLe (2 ^ q), (1 + 4 / (p : ℝ))) / 2 ^ (20 * l + 1)
        = (2 : ℝ) ^ m * ((∏ p ∈ oddPrimesLe (2 ^ q), (1 + 4 / (p : ℝ))) / 2 ^ (20 * l + 1)) := by
          ring
      _ ≤ _ := h
  have hE1' : ((2 ^ q : ℕ) : ℝ) + 1 ≤ (2 / 2 ^ (m / 2)) * (2 : ℝ) ^ m := by
    have : 2 * ((2 : ℝ) ^ m / 2 ^ (m / 2)) = (2 / 2 ^ (m / 2)) * (2 : ℝ) ^ m := by ring
    linarith [hE1]
  have hE4' : (((20 * l : ℕ) : ℝ) + 1) * (2 * ((2 ^ q : ℕ) : ℝ) + 3) ^ (20 * l)
      ≤ (21 * (m : ℝ) ^ 41 / 2 ^ (m / 2)) * (2 : ℝ) ^ m := by
    have : 21 * (m : ℝ) ^ 41 * ((2 : ℝ) ^ m / 2 ^ (m / 2))
        = (21 * (m : ℝ) ^ 41 / 2 ^ (m / 2)) * (2 : ℝ) ^ m := by ring
    linarith [hE4]
  have hexpand : (2 / 2 ^ (m / 2) + 416000 * (l : ℝ) ^ 2 / (m : ℝ) ^ 2
      + Real.exp 20 * 2 ^ 19 / (m : ℝ) ^ 4 + 21 * (m : ℝ) ^ 41 / 2 ^ (m / 2)) * (2 : ℝ) ^ m
      = (2 / 2 ^ (m / 2)) * (2 : ℝ) ^ m + (2 : ℝ) ^ m * (416000 * (l : ℝ) ^ 2 / (m : ℝ) ^ 2)
        + (2 : ℝ) ^ m * (Real.exp 20 * 2 ^ 19 / (m : ℝ) ^ 4)
        + (21 * (m : ℝ) ^ 41 / 2 ^ (m / 2)) * (2 : ℝ) ^ m := by ring
  rw [hexpand]
  push_cast at hsieve hE1' hE4' ⊢
  linarith

/-- The explicit bound coming from Brun's sieve with `z = 2 ^ (m / (40 log₂ m))` and
`k = 20 log₂ m`. -/
lemma twinCount_two_pow_bound {m : ℕ} (hm : 1024 ≤ m) :
    (twinCount (2 ^ m) : ℝ) / 2 ^ m
      ≤ 2 / 2 ^ (m / 2) + 416000 * ((Nat.log 2 m : ℝ)) ^ 2 / (m : ℝ) ^ 2
        + Real.exp 20 * 2 ^ 19 / (m : ℝ) ^ 4 + 21 * (m : ℝ) ^ 41 / 2 ^ (m / 2) := by
  obtain ⟨l, hl⟩ : ∃ l, l = Nat.log 2 m := ⟨_, rfl⟩
  rw [← hl]
  have hl10 : 10 ≤ l := by
    have h1 : Nat.log 2 1024 ≤ Nat.log 2 m := Nat.log_mono_right hm
    have h2 : Nat.log 2 1024 = 10 := by norm_num
    omega
  have hpowl : 2 ^ l ≤ m := by
    rw [hl]
    exact Nat.pow_log_le_self 2 (by omega)
  have hpowl2 : m < 2 * 2 ^ l := by
    have h := Nat.lt_pow_succ_log_self (show 1 < 2 by norm_num) m
    rw [← hl] at h
    calc m < 2 ^ (l + 1) := h
      _ = 2 * 2 ^ l := by ring
  have h80 : 80 * l ≤ m := le_trans (eighty_mul_le_two_pow hl10) hpowl
  obtain ⟨q, hq⟩ : ∃ q, q = m / (40 * l) := ⟨_, rfl⟩
  have hq2 : 2 ≤ q := by
    rw [hq, Nat.le_div_iff_mul_le (by omega)]
    omega
  have hqm : 40 * l * q ≤ m := by
    rw [hq]
    exact Nat.mul_div_le m (40 * l)
  have hqup : m < (q + 1) * (40 * l) := by
    rw [← Nat.div_lt_iff_lt_mul (show 0 < 40 * l by omega), ← hq]
    omega
  exact twinCount_two_pow_bound_gen hm hl10 hpowl hpowl2 hq2 hqm hqup

theorem summable_twinCount_div_two_pow :
    Summable (fun m : ℕ => (twinCount (2 ^ m) : ℝ) / 2 ^ m) := by
  obtain ⟨C0, hC0pos, hC0⟩ := poly_div_two_pow_half_le 0
  obtain ⟨C41, hC41pos, hC41⟩ := poly_div_two_pow_half_le 41
  obtain ⟨Cl, hClpos, hCl⟩ := log_sq_le
  have hbound : ∀ m : ℕ, 1024 ≤ m → (twinCount (2 ^ m) : ℝ) / 2 ^ m
      ≤ (2 * C0 + 416000 * Cl + Real.exp 20 * 2 ^ 19 + 21 * C41)
          * (Real.sqrt m / (m : ℝ) ^ 2) := by
    intro m hm
    have hmpos : (0 : ℝ) < (m : ℝ) := by
      have : 0 < m := by omega
      exact_mod_cast this
    have hmR : (1024 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    have hm1 : (1 : ℝ) ≤ Real.sqrt m := by
      have h1 : (1 : ℝ) ≤ (m : ℝ) := by linarith
      calc (1 : ℝ) = Real.sqrt 1 := by simp
        _ ≤ Real.sqrt m := Real.sqrt_le_sqrt h1
    have key : ∀ c : ℝ, 0 ≤ c → c / (m : ℝ) ^ 2 ≤ c * (Real.sqrt m / (m : ℝ) ^ 2) := by
      intro c hc
      have h1 : c ≤ c * Real.sqrt m := by nlinarith
      calc c / (m : ℝ) ^ 2 ≤ (c * Real.sqrt m) / (m : ℝ) ^ 2 := by gcongr
        _ = c * (Real.sqrt m / (m : ℝ) ^ 2) := by ring
    have hb := twinCount_two_pow_bound hm
    -- term 1
    have h0 := hC0 m (by omega)
    rw [pow_zero] at h0
    have t1 : 2 / (2 : ℝ) ^ (m / 2) ≤ (2 * C0) * (Real.sqrt m / (m : ℝ) ^ 2) := by
      have h2 : 2 / (2 : ℝ) ^ (m / 2) = 2 * (1 / (2 : ℝ) ^ (m / 2)) := by ring
      have h3 : 2 * (1 / (2 : ℝ) ^ (m / 2)) ≤ 2 * (C0 / (m : ℝ) ^ 2) := by linarith
      have h4 : 2 * (C0 / (m : ℝ) ^ 2) = (2 * C0) / (m : ℝ) ^ 2 := by ring
      linarith [key (2 * C0) (by positivity)]
    -- term 2
    have hL := hCl m (by omega)
    have t2 : 416000 * ((Nat.log 2 m : ℝ)) ^ 2 / (m : ℝ) ^ 2
        ≤ (416000 * Cl) * (Real.sqrt m / (m : ℝ) ^ 2) := by
      have hnum : 416000 * ((Nat.log 2 m : ℝ)) ^ 2 ≤ 416000 * (Cl * Real.sqrt m) := by linarith
      calc 416000 * ((Nat.log 2 m : ℝ)) ^ 2 / (m : ℝ) ^ 2
          ≤ (416000 * (Cl * Real.sqrt m)) / (m : ℝ) ^ 2 := by gcongr
        _ = (416000 * Cl) * (Real.sqrt m / (m : ℝ) ^ 2) := by ring
    -- term 3
    have t3 : Real.exp 20 * 2 ^ 19 / (m : ℝ) ^ 4
        ≤ (Real.exp 20 * 2 ^ 19) * (Real.sqrt m / (m : ℝ) ^ 2) := by
      have hp24 : (m : ℝ) ^ 2 ≤ (m : ℝ) ^ 4 := pow_le_pow_right₀ (by linarith) (by norm_num)
      have hp4 : (0 : ℝ) < (m : ℝ) ^ 4 := by positivity
      have hcmp : (1 : ℝ) / (m : ℝ) ^ 4 ≤ Real.sqrt m / (m : ℝ) ^ 2 := by
        rw [div_le_div_iff₀ hp4 (by positivity)]
        nlinarith
      have hE : Real.exp 20 * 2 ^ 19 / (m : ℝ) ^ 4
          = (Real.exp 20 * 2 ^ 19) * (1 / (m : ℝ) ^ 4) := by ring
      have hpos : (0 : ℝ) ≤ Real.exp 20 * 2 ^ 19 := by positivity
      rw [hE]
      exact mul_le_mul_of_nonneg_left hcmp hpos
    -- term 4
    have h41 := hC41 m (by omega)
    have t4 : 21 * (m : ℝ) ^ 41 / (2 : ℝ) ^ (m / 2) ≤ (21 * C41) * (Real.sqrt m / (m : ℝ) ^ 2) := by
      have h2 : 21 * (m : ℝ) ^ 41 / (2 : ℝ) ^ (m / 2) = 21 * ((m : ℝ) ^ 41 / (2 : ℝ) ^ (m / 2)) := by
        ring
      have h3 : 21 * ((m : ℝ) ^ 41 / (2 : ℝ) ^ (m / 2)) ≤ 21 * (C41 / (m : ℝ) ^ 2) := by linarith
      have h4 : 21 * (C41 / (m : ℝ) ^ 2) = (21 * C41) / (m : ℝ) ^ 2 := by ring
      linarith [key (21 * C41) (by positivity)]
    nlinarith [t1, t2, t3, t4, hb]
  have hS : Summable (fun m : ℕ => (2 * C0 + 416000 * Cl + Real.exp 20 * 2 ^ 19 + 21 * C41)
      * (Real.sqrt m / (m : ℝ) ^ 2)) :=
    summable_sqrt_div_sq.mul_left _
  have hS' : Summable (fun n : ℕ => (2 * C0 + 416000 * Cl + Real.exp 20 * 2 ^ 19 + 21 * C41)
      * (Real.sqrt ((n + 1024 : ℕ)) / ((n + 1024 : ℕ) : ℝ) ^ 2)) :=
    (summable_nat_add_iff 1024).mpr hS
  rw [← summable_nat_add_iff 1024]
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hS'
  exact hbound (n + 1024) (by omega)

end Brun

import Mathlib

/-!
# Bonferroni inequalities

Truncated inclusion-exclusion: for an even truncation level `k`, the alternating partial sum
of binomial coefficients is an upper bound for the indicator of "no condition holds".
-/

namespace Brun

open Finset

/-- The alternating partial sum of binomial coefficients. -/
lemma alt_choose_sum (m k : ℕ) (hm : 1 ≤ m) :
    ∑ j ∈ range (k + 1), (-1 : ℝ) ^ j * (m.choose j : ℝ)
      = (-1) ^ k * ((m - 1).choose k : ℝ) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Finset.sum_range_succ, ih]
      obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      rw [Nat.choose_succ_succ m' k]
      push_cast
      ring

lemma bonferroni_choose (m k : ℕ) (hk : Even k) :
    (if m = 0 then (1 : ℝ) else 0) ≤ ∑ j ∈ range (k + 1), (-1 : ℝ) ^ j * (m.choose j : ℝ) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp only [if_pos rfl]
    rw [Finset.sum_eq_single 0]
    · simp
    · intro j _ hj
      simp [Nat.choose_eq_zero_of_lt (Nat.pos_of_ne_zero hj)]
    · intro h; simp at h
  · rw [if_neg (by omega), alt_choose_sum m k hm, hk.neg_one_pow]
    positivity

/-- Set-theoretic Bonferroni inequality: the indicator that no `p ∈ P` satisfies `Q` is at most
the truncated (at even level `k`) inclusion-exclusion sum. -/
lemma bonferroni_sets {α : Type*} [DecidableEq α] (P : Finset α) (Q : α → Prop)
    [DecidablePred Q] (k : ℕ) (hk : Even k) :
    (if ∀ p ∈ P, ¬ Q p then (1 : ℝ) else 0)
      ≤ ∑ j ∈ range (k + 1), (-1 : ℝ) ^ j *
          (((P.powersetCard j).filter (fun S => ∀ p ∈ S, Q p)).card : ℝ) := by
  have hfilter : ∀ j, (P.powersetCard j).filter (fun S => ∀ p ∈ S, Q p)
      = (P.filter Q).powersetCard j := by
    intro j
    ext S
    simp only [Finset.mem_filter, Finset.mem_powersetCard]
    constructor
    · rintro ⟨⟨hSP, hcard⟩, hQ⟩
      exact ⟨fun x hx => Finset.mem_filter.mpr ⟨hSP hx, hQ x hx⟩, hcard⟩
    · rintro ⟨hSP, hcard⟩
      refine ⟨⟨fun x hx => (Finset.mem_filter.mp (hSP hx)).1, hcard⟩, ?_⟩
      exact fun x hx => (Finset.mem_filter.mp (hSP hx)).2
  have hcard : ∀ j, (((P.powersetCard j).filter (fun S => ∀ p ∈ S, Q p)).card : ℝ)
      = ((P.filter Q).card.choose j : ℝ) := by
    intro j; rw [hfilter j, Finset.card_powersetCard]
  simp only [hcard]
  have hkey := bonferroni_choose (P.filter Q).card k hk
  refine le_trans ?_ hkey
  by_cases h : ∀ p ∈ P, ¬ Q p
  · rw [if_pos h, if_pos]
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    exact h
  · rw [if_neg h]
    split <;> norm_num

end Brun

import RequestProject.Brun.Asymptotics
import RequestProject.Brun.Dyadic

/-!
# Brun's theorem

Combining the dyadic decomposition with the asymptotic bound for `twinCount (2^m)`
we obtain the summability of the twin prime indicator series `∑ 1/p`.
-/

namespace Brun

/-- The dyadic input needed for `summable_twinIndicator`. -/
theorem summable_twinCount_shift :
    Summable (fun m : ℕ => (twinCount (2 ^ (m + 1)) : ℝ) / 2 ^ m) := by
  have h : Summable (fun m : ℕ => (twinCount (2 ^ (m + 1)) : ℝ) / 2 ^ (m + 1)) :=
    (summable_nat_add_iff 1).mpr summable_twinCount_div_two_pow
  refine (h.mul_left 2).congr (fun m => ?_)
  rw [pow_succ]
  field_simp
  ring

/-- Brun's theorem: the sum of the reciprocals of the twin primes converges. -/
theorem summable_twinIndicator' : Summable twinIndicator :=
  summable_twinIndicator summable_twinCount_shift

end Brun

import RequestProject.Brun.Defs

/-!
# Counting solutions of `n (n+2) ≡ 0` in an interval

The main result is `Brun.abs_dvdCount_sub_le`: for a finite set `S` of odd primes, the number of
`n < N` with `∏_{p ∈ S} p ∣ n (n+2)` differs from `2^{|S|} N / ∏ p` by at most `2^{|S|}`.
-/

namespace Brun

open Finset

/-- Counting a residue class in `range N`: upper bound. -/
lemma card_filter_mod_le (N m r : ℕ) :
    ((range N).filter (fun n => n % m = r)).card ≤ N / m + 1 := by
  have h : ((range N).filter (fun n => n % m = r)).card ≤ (range (N / m + 1)).card := by
    refine Finset.card_le_card_of_injOn (fun n => n / m) ?_ ?_
    · intro n hn
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hn
      simp only [Finset.mem_coe, Finset.mem_range]
      have : n / m ≤ N / m := Nat.div_le_div_right hn.1.le
      omega
    · intro n hn n' hn' h
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hn hn'
      simp only at h
      have e1 := Nat.div_add_mod n m
      have e2 := Nat.div_add_mod n' m
      rw [hn.2] at e1
      rw [hn'.2] at e2
      rw [h] at e1
      omega
  simpa using h

/-- Counting a residue class in `range N`: lower bound. -/
lemma le_card_filter_mod (N m r : ℕ) (hr : r < m) :
    N / m ≤ ((range N).filter (fun n => n % m = r)).card := by
  have h : (range (N / m)).card ≤ ((range N).filter (fun n => n % m = r)).card := by
    refine Finset.card_le_card_of_injOn (fun q => q * m + r) ?_ ?_
    · intro q hq
      simp only [Finset.mem_coe, Finset.mem_range] at hq
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range]
      refine ⟨?_, by simp [Nat.mod_eq_of_lt hr]⟩
      have h1 : (q + 1) * m ≤ (N / m) * m := Nat.mul_le_mul_right m hq
      have h2 : (N / m) * m ≤ N := Nat.div_mul_le_self N m
      have : q * m + m ≤ N := by nlinarith [h1, h2]
      omega
    · intro q _ q' _ h
      simp only at h
      have hm : 0 < m := by omega
      have : q * m = q' * m := by omega
      exact Nat.eq_of_mul_eq_mul_right hm this
  simpa using h

lemma abs_card_filter_mod_sub_le (N m r : ℕ) (hr : r < m) :
    |(((range N).filter (fun n => n % m = r)).card : ℝ) - (N : ℝ) / m| ≤ 1 := by
  have hm : 0 < m := by omega
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have h1 := card_filter_mod_le N m r
  have h2 := le_card_filter_mod N m r hr
  have hfl : ((N / m : ℕ) : ℝ) ≤ (N : ℝ) / m := Nat.cast_div_le
  have hfl2 : (N : ℝ) / m < ((N / m : ℕ) : ℝ) + 1 := by
    rw [div_lt_iff₀ hmR]
    have hdm := Nat.div_add_mod N m
    have hlt := Nat.mod_lt N hm
    have : N < (N / m + 1) * m := by
      have : (N / m + 1) * m = m * (N / m) + m := by ring
      omega
    exact_mod_cast this
  have h1R : (((range N).filter (fun n => n % m = r)).card : ℝ) ≤ ((N / m : ℕ) : ℝ) + 1 := by
    exact_mod_cast h1
  have h2R : ((N / m : ℕ) : ℝ) ≤ (((range N).filter (fun n => n % m = r)).card : ℝ) := by
    exact_mod_cast h2
  rw [abs_le]
  constructor <;> linarith

/-- The number of `n < N` in a fixed pair of coprime congruence conditions. -/
lemma abs_card_filter_pair_sub_le (N a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hab : Nat.Coprime a b) :
    |(((range N).filter (fun n => a ∣ n ∧ b ∣ (n + 2))).card : ℝ) - (N : ℝ) / (a * b)| ≤ 1 := by
  -- find a solution of the pair of congruences
  obtain ⟨k, hk1, hk2⟩ := Nat.chineseRemainder hab 0 (b * b - 2)
  have hab0 : 0 < a * b := Nat.mul_pos ha hb
  set r := k % (a * b) with hr_def
  have hrlt : r < a * b := Nat.mod_lt _ hab0
  have hkr : r ≡ k [MOD a * b] := Nat.mod_modEq k (a * b)
  have hra : a ∣ r := by
    have : r ≡ k [MOD a] := hkr.of_dvd ⟨b, rfl⟩
    have : r ≡ 0 [MOD a] := this.trans hk1
    simpa [Nat.modEq_zero_iff_dvd] using this
  have hrb : b ∣ r + 2 := by
    rcases Nat.lt_or_ge b 2 with hb2 | hb2
    · interval_cases b
      · exact one_dvd _
    · have h2 : r ≡ k [MOD b] := hkr.of_dvd ⟨a, mul_comm a b⟩
      have h3 : r ≡ b * b - 2 [MOD b] := h2.trans hk2
      have h4 : r + 2 ≡ (b * b - 2) + 2 [MOD b] := h3.add_right 2
      have h5 : (b * b - 2) + 2 = b * b := by
        have : 2 ≤ b * b := by nlinarith
        omega
      rw [h5] at h4
      have : b ∣ b * b := ⟨b, rfl⟩
      exact (Nat.modEq_zero_iff_dvd.mp (h4.trans ((Nat.modEq_zero_iff_dvd).mpr this)))
  have hset : (range N).filter (fun n => a ∣ n ∧ b ∣ (n + 2))
      = (range N).filter (fun n => n % (a * b) = r) := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_range, and_congr_right_iff]
    intro _
    constructor
    · rintro ⟨hna, hnb⟩
      have e1 : n ≡ r [MOD a] := by
        have h1 : n ≡ 0 [MOD a] := (Nat.modEq_zero_iff_dvd).mpr hna
        have h2 : r ≡ 0 [MOD a] := (Nat.modEq_zero_iff_dvd).mpr hra
        exact h1.trans h2.symm
      have e2 : n ≡ r [MOD b] := by
        have h1 : n + 2 ≡ 0 [MOD b] := (Nat.modEq_zero_iff_dvd).mpr hnb
        have h2 : r + 2 ≡ 0 [MOD b] := (Nat.modEq_zero_iff_dvd).mpr hrb
        have : n + 2 ≡ r + 2 [MOD b] := h1.trans h2.symm
        exact Nat.ModEq.add_right_cancel' 2 this
      have : n ≡ r [MOD a * b] := (Nat.modEq_and_modEq_iff_modEq_mul hab).mp ⟨e1, e2⟩
      calc n % (a * b) = r % (a * b) := this
        _ = r := Nat.mod_eq_of_lt hrlt
    · intro hn
      have hmod : n ≡ r [MOD a * b] := by
        unfold Nat.ModEq
        rw [hn, Nat.mod_eq_of_lt hrlt]
      have e1 : n ≡ r [MOD a] := hmod.of_dvd ⟨b, rfl⟩
      have e2 : n ≡ r [MOD b] := hmod.of_dvd ⟨a, mul_comm a b⟩
      refine ⟨?_, ?_⟩
      · have : n ≡ 0 [MOD a] := e1.trans ((Nat.modEq_zero_iff_dvd).mpr hra)
        exact (Nat.modEq_zero_iff_dvd).mp this
      · have h1 : n + 2 ≡ r + 2 [MOD b] := e2.add_right 2
        have : n + 2 ≡ 0 [MOD b] := h1.trans ((Nat.modEq_zero_iff_dvd).mpr hrb)
        exact (Nat.modEq_zero_iff_dvd).mp this
  rw [hset]
  have := abs_card_filter_mod_sub_le N (a * b) r hrlt
  simpa using this

/-- The fibre decomposition of the set counted by `dvdCount`. -/
lemma dvdCount_fiber_eq (N : ℕ) (S : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p ∧ p ≠ 2)
    {T : Finset ℕ} (hT : T ⊆ S) :
    ((range N).filter (fun n => ∀ p ∈ S, p ∣ n * (n + 2))).filter
        (fun n => S.filter (fun p => p ∣ n) = T)
      = (range N).filter (fun n => (∏ p ∈ T, p) ∣ n ∧ (∏ p ∈ S \ T, p) ∣ (n + 2)) := by
  ext n
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨⟨hn, hdvd⟩, hfib⟩
    refine ⟨hn, ?_, ?_⟩
    · refine Finset.prod_primes_dvd n (fun p hp => (hS p (hT hp)).1.prime) (fun p hp => ?_)
      have : p ∈ S.filter (fun p => p ∣ n) := by rw [hfib]; exact hp
      exact (Finset.mem_filter.mp this).2
    · refine Finset.prod_primes_dvd (n + 2) (fun p hp => (hS p (Finset.mem_sdiff.mp hp).1).1.prime)
        (fun p hp => ?_)
      obtain ⟨hpS, hpT⟩ := Finset.mem_sdiff.mp hp
      have hpn : ¬ p ∣ n := by
        intro h
        exact hpT (by rw [← hfib]; exact Finset.mem_filter.mpr ⟨hpS, h⟩)
      have := (hS p hpS).1.dvd_mul.mp (hdvd p hpS)
      tauto
  · rintro ⟨hn, hT1, hT2⟩
    have hdvd : ∀ p ∈ S, p ∣ n * (n + 2) := by
      intro p hp
      by_cases hpT : p ∈ T
      · exact Dvd.dvd.mul_right (dvd_trans (Finset.dvd_prod_of_mem _ hpT) hT1) _
      · have : p ∈ S \ T := Finset.mem_sdiff.mpr ⟨hp, hpT⟩
        exact Dvd.dvd.mul_left (dvd_trans (Finset.dvd_prod_of_mem _ this) hT2) _
    refine ⟨⟨hn, hdvd⟩, ?_⟩
    ext p
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hpS, hpn⟩
      by_contra hpT
      have hmem : p ∈ S \ T := Finset.mem_sdiff.mpr ⟨hpS, hpT⟩
      have hp2 : p ∣ n + 2 := dvd_trans (Finset.dvd_prod_of_mem _ hmem) hT2
      have hdvd2 : p ∣ 2 := (Nat.dvd_add_iff_right hpn).mpr hp2
      have h1 := (hS p hpS).1.two_le
      have h2 := (hS p hpS).2
      have := Nat.le_of_dvd (by norm_num) hdvd2
      omega
    · intro hpT
      exact ⟨hT hpT, dvd_trans (Finset.dvd_prod_of_mem _ hpT) hT1⟩

/-- If each of finitely many quantities is within `1` of `c`, their sum is within `#s` of
`#s * c`. -/
lemma abs_sum_sub_card_mul_le {α : Type*} (s : Finset α) (f : α → ℝ) (c : ℝ)
    (h : ∀ T ∈ s, |f T - c| ≤ 1) : |(∑ T ∈ s, f T) - s.card * c| ≤ s.card := by
  have heq : (∑ T ∈ s, f T) - s.card * c = ∑ T ∈ s, (f T - c) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
  rw [heq]
  calc |∑ T ∈ s, (f T - c)| ≤ ∑ T ∈ s, |f T - c| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _T ∈ s, (1 : ℝ) := Finset.sum_le_sum h
    _ = s.card := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]

/-- Main counting estimate. -/
lemma abs_dvdCount_sub_le (N : ℕ) (S : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p ∧ p ≠ 2) :
    |(dvdCount N S : ℝ) - 2 ^ S.card * (N : ℝ) / (∏ p ∈ S, (p : ℝ))| ≤ 2 ^ S.card := by
  have hfib : dvdCount N S
      = ∑ T ∈ S.powerset, (((range N).filter (fun n => ∀ p ∈ S, p ∣ n * (n + 2))).filter
          (fun n => S.filter (fun p => p ∣ n) = T)).card :=
    Finset.card_eq_sum_card_fiberwise
      (fun n _ => Finset.mem_powerset.mpr (Finset.filter_subset _ _))
  have hprodpos : (0 : ℝ) < ∏ p ∈ S, (p : ℝ) := by
    refine Finset.prod_pos (fun p hp => ?_)
    exact_mod_cast (hS p hp).1.pos
  have key : ∀ T ∈ S.powerset,
      |(((((range N).filter (fun n => ∀ p ∈ S, p ∣ n * (n + 2))).filter
          (fun n => S.filter (fun p => p ∣ n) = T)).card : ℕ) : ℝ)
        - (N : ℝ) / (∏ p ∈ S, (p : ℝ))| ≤ 1 := by
    intro T hT
    have hTS : T ⊆ S := Finset.mem_powerset.mp hT
    rw [dvdCount_fiber_eq N S hS hTS]
    set a := ∏ p ∈ T, p with ha
    set b := ∏ p ∈ S \ T, p with hb
    have hapos : 0 < a := Finset.prod_pos (fun p hp => (hS p (hTS hp)).1.pos)
    have hbpos : 0 < b := Finset.prod_pos (fun p hp => (hS p (Finset.mem_sdiff.mp hp).1).1.pos)
    have hab : Nat.Coprime a b := by
      refine Nat.Coprime.prod_left (fun p hp => Nat.Coprime.prod_right (fun q hq => ?_))
      obtain ⟨hqS, hqT⟩ := Finset.mem_sdiff.mp hq
      have hpne : p ≠ q := by rintro rfl; exact hqT hp
      exact (Nat.coprime_primes (hS p (hTS hp)).1 (hS q hqS).1).mpr hpne
    have hmul : (a : ℝ) * (b : ℝ) = ∏ p ∈ S, (p : ℝ) := by
      have hba : b * a = ∏ p ∈ S, p := Finset.prod_sdiff hTS
      have h2 : a * b = ∏ p ∈ S, p := by rw [← hba]; ring
      calc (a : ℝ) * (b : ℝ) = ((a * b : ℕ) : ℝ) := by push_cast; ring
        _ = ((∏ p ∈ S, p : ℕ) : ℝ) := by rw [h2]
        _ = ∏ p ∈ S, (p : ℝ) := by push_cast; ring
    have hpair := abs_card_filter_pair_sub_le N a b hapos hbpos hab
    rw [hmul] at hpair
    exact hpair
  have hmain := abs_sum_sub_card_mul_le S.powerset
    (fun T => ((((range N).filter (fun n => ∀ p ∈ S, p ∣ n * (n + 2))).filter
      (fun n => S.filter (fun p => p ∣ n) = T)).card : ℝ))
    ((N : ℝ) / (∏ p ∈ S, (p : ℝ))) key
  rw [Finset.card_powerset] at hmain
  have hcast : ((dvdCount N S : ℕ) : ℝ)
      = ∑ T ∈ S.powerset, ((((range N).filter (fun n => ∀ p ∈ S, p ∣ n * (n + 2))).filter
          (fun n => S.filter (fun p => p ∣ n) = T)).card : ℝ) := by
    rw [hfib]; push_cast; ring
  rw [hcast]
  have : (2 : ℝ) ^ S.card * (N : ℝ) / (∏ p ∈ S, (p : ℝ))
      = ((2 ^ S.card : ℕ) : ℝ) * ((N : ℝ) / (∏ p ∈ S, (p : ℝ))) := by
    push_cast; ring
  rw [this]
  simpa using hmain

end Brun

import RequestProject.Brun.Defs

/-!
# Elementary estimates for sums and products over primes

* `Brun.prod_primesBelow_one_sub_inv_le` : `∏_{p ≤ z} (1 - 1/p) ≤ e / log z`, proved from the
  Euler product over smooth numbers.
* `Brun.sum_inv_primesBelow_pow_two_le` : `∑_{p ≤ 2^q} 1/p ≤ 5 + 4 log q`, proved from the
  bound `∏_{p ≤ n} p ≤ 4 ^ n` on the primorial.
-/

namespace Brun

open Finset

/-! ### The Euler product bound -/

/-- The completely multiplicative function `n ↦ n ^ (-s)`. -/
noncomputable def rpowHom (s : ℝ) : ℕ →* ℝ where
  toFun := fun n => (n : ℝ) ^ (-s)
  map_one' := by simp
  map_mul' := by
    intro m n
    push_cast
    rw [Real.mul_rpow (by positivity) (by positivity)]

lemma rpowHom_apply (s : ℝ) (n : ℕ) : (rpowHom s) n = (n : ℝ) ^ (-s) := rfl

/-- Comparison of a partial sum of `n ^ (-s)` with the Euler product over the primes `≤ z`. -/
lemma sum_rpow_le_prod_primesBelow (z : ℕ) {s : ℝ} (hs : 1 < s) :
    ∑ n ∈ Icc 1 z, (n : ℝ) ^ (-s) ≤ ∏ p ∈ Nat.primesBelow (z + 1), (1 - (p : ℝ) ^ (-s))⁻¹ := by
  have hsum : Summable (rpowHom s) := by
    have : Summable (fun n : ℕ => (n : ℝ) ^ (-s)) := by
      rw [Real.summable_nat_rpow]; linarith
    exact this
  have heq := EulerProduct.prod_primesBelow_geometric_eq_tsum_smoothNumbers hsum (z + 1)
  simp only [rpowHom_apply] at heq
  rw [heq]
  have hmem : ∀ n ∈ Icc 1 z, n ∈ Nat.smoothNumbers (z + 1) := by
    intro n hn
    simp only [Finset.mem_Icc] at hn
    rw [Nat.mem_smoothNumbers]
    refine ⟨by omega, fun p hp => ?_⟩
    have := Nat.le_of_mem_primeFactorsList hp
    omega
  set T : Finset (Nat.smoothNumbers (z + 1)) := (Icc 1 z).subtype _ with hT
  have h1 : ∑ x ∈ T, (rpowHom s) x = ∑ n ∈ Icc 1 z, (n : ℝ) ^ (-s) := by
    rw [hT, Finset.sum_subtype_eq_sum_filter, Finset.filter_true_of_mem hmem]
    rfl
  have hsub : Summable (fun x : Nat.smoothNumbers (z + 1) => (rpowHom s) x) := hsum.subtype _
  have h2 : ∑ x ∈ T, (rpowHom s) x ≤ ∑' m : Nat.smoothNumbers (z + 1), (rpowHom s) m := by
    refine Summable.sum_le_tsum T (fun i _ => ?_) hsub
    rw [rpowHom_apply]
    positivity
  rw [← h1]
  exact h2

/-- `∏_{p ≤ z} (1 - 1/p) ≤ e / log z`. -/
lemma prod_primesBelow_one_sub_inv_le {z : ℕ} (hz : 3 ≤ z) :
    ∏ p ∈ Nat.primesBelow (z + 1), (1 - 1 / (p : ℝ)) ≤ Real.exp 1 / Real.log z := by
  have hzR : (3 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz
  have hlogpos : 1 < Real.log z := by
    have : Real.log 3 ≤ Real.log z := Real.log_le_log (by norm_num) hzR
    have h3 : 1 < Real.log 3 := by
      have hlt : Real.log (Real.exp 1) < Real.log 3 :=
        Real.log_lt_log (Real.exp_pos 1) (by linarith [Real.exp_one_lt_d9])
      rwa [Real.log_exp] at hlt
    linarith
  set s : ℝ := 1 + 1 / Real.log z with hs_def
  have hs1 : 1 < s := by
    rw [hs_def]
    have : 0 < 1 / Real.log z := by positivity
    linarith
  -- lower bound for the partial sum
  have hlow : Real.exp (-1) * ∑ n ∈ Icc 1 z, (1 / (n : ℝ)) ≤ ∑ n ∈ Icc 1 z, (n : ℝ) ^ (-s) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun n hn => ?_)
    simp only [Finset.mem_Icc] at hn
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn.1
    have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
    have hlogn : 0 ≤ Real.log n := Real.log_nonneg hn1
    have hlognz : Real.log n ≤ Real.log z := by
      apply Real.log_le_log hnpos
      exact_mod_cast hn.2
    rw [Real.rpow_def_of_pos hnpos]
    have h1 : (1 : ℝ) / (n : ℝ) = Real.exp (-Real.log n) := by
      rw [Real.exp_neg, Real.exp_log hnpos]
      simp
    rw [h1, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have : Real.log n * (1 / Real.log z) ≤ 1 := by
      rw [mul_one_div, div_le_one (by linarith)]
      exact hlognz
    rw [hs_def]
    nlinarith
  -- upper bound for the Euler factors
  have hup : ∏ p ∈ Nat.primesBelow (z + 1), (1 - (p : ℝ) ^ (-s))⁻¹
      ≤ ∏ p ∈ Nat.primesBelow (z + 1), (1 - 1 / (p : ℝ))⁻¹ := by
    refine Finset.prod_le_prod (fun p hp => ?_) (fun p hp => ?_)
    · have hp2 : 2 ≤ p := (Nat.prime_of_mem_primesBelow hp).two_le
      have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp2
      have : (p : ℝ) ^ (-s) ≤ 1 := by
        apply Real.rpow_le_one_of_one_le_of_nonpos (by linarith)
        linarith
      have hlt : (p : ℝ) ^ (-s) < 1 := by
        have : (p : ℝ) ^ (-s) < (p : ℝ) ^ (0 : ℝ) := by
          apply Real.rpow_lt_rpow_of_exponent_lt (by linarith)
          linarith
        simpa using this
      have : 0 < 1 - (p : ℝ) ^ (-s) := by linarith
      positivity
    · have hp2 : 2 ≤ p := (Nat.prime_of_mem_primesBelow hp).two_le
      have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp2
      have hppos : (0 : ℝ) < (p : ℝ) := by linarith
      have hle : (p : ℝ) ^ (-s) ≤ (p : ℝ) ^ (-1 : ℝ) := by
        apply Real.rpow_le_rpow_of_exponent_le (by linarith)
        linarith
      have hinv : (p : ℝ) ^ (-1 : ℝ) = 1 / (p : ℝ) := by
        rw [Real.rpow_neg_one]; simp
      rw [hinv] at hle
      have h1 : 0 < 1 - 1 / (p : ℝ) := by
        have : 1 / (p : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hpR
        linarith
      exact inv_anti₀ h1 (by linarith)
  -- harmonic sum lower bound
  have hharm : Real.log z ≤ ∑ n ∈ Icc 1 z, (1 / (n : ℝ)) := by
    have h1 : Real.log ((z : ℝ)) ≤ Real.log ((z : ℕ) + 1 : ℕ) := by
      apply Real.log_le_log (by linarith)
      push_cast
      linarith
    have h2 := log_add_one_le_harmonic z
    have h3 : ((harmonic z : ℚ) : ℝ) = ∑ n ∈ Icc 1 z, (1 / (n : ℝ)) := by
      rw [harmonic_eq_sum_Icc]
      push_cast
      simp [one_div]
    rw [h3] at h2
    exact le_trans h1 h2
  have hkey := sum_rpow_le_prod_primesBelow z hs1
  have hprodpos : 0 < ∏ p ∈ Nat.primesBelow (z + 1), (1 - 1 / (p : ℝ)) := by
    refine Finset.prod_pos (fun p hp => ?_)
    have hp2 : 2 ≤ p := (Nat.prime_of_mem_primesBelow hp).two_le
    have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp2
    have : 1 / (p : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hpR
    linarith
  have hinvprod : ∏ p ∈ Nat.primesBelow (z + 1), (1 - 1 / (p : ℝ))⁻¹
      = (∏ p ∈ Nat.primesBelow (z + 1), (1 - 1 / (p : ℝ)))⁻¹ := by
    rw [← Finset.prod_inv_distrib]
  rw [hinvprod] at hup
  -- combine
  have hchain : Real.exp (-1) * Real.log z
      ≤ (∏ p ∈ Nat.primesBelow (z + 1), (1 - 1 / (p : ℝ)))⁻¹ := by
    calc Real.exp (-1) * Real.log z
        ≤ Real.exp (-1) * ∑ n ∈ Icc 1 z, (1 / (n : ℝ)) := by
          apply mul_le_mul_of_nonneg_left hharm (le_of_lt (Real.exp_pos _))
      _ ≤ ∑ n ∈ Icc 1 z, (n : ℝ) ^ (-s) := hlow
      _ ≤ _ := le_trans hkey hup
  rw [le_inv_comm₀ (by positivity) hprodpos] at hchain
  calc ∏ p ∈ Nat.primesBelow (z + 1), (1 - 1 / (p : ℝ))
      ≤ (Real.exp (-1) * Real.log z)⁻¹ := hchain
    _ = Real.exp 1 / Real.log z := by
        rw [Real.exp_neg]
        field_simp

/-! ### Mertens-type upper bound via the primorial -/

/-- The number of primes in `(2^j, 2^(j+1)]` is at most `2^(j+2)/j`. -/
lemma card_primes_block_mul_le (j : ℕ) :
    (((range (2 ^ (j + 1) + 1)).filter (fun p => Nat.Prime p ∧ 2 ^ j < p)).card) * j
      ≤ 2 ^ (j + 2) := by
  set B := (range (2 ^ (j + 1) + 1)).filter (fun p => Nat.Prime p ∧ 2 ^ j < p) with hB
  have hsub : B ⊆ (range (2 ^ (j + 1) + 1)).filter (fun p => Nat.Prime p) := by
    intro p hp
    rw [hB, Finset.mem_filter] at hp
    exact Finset.mem_filter.mpr ⟨hp.1, hp.2.1⟩
  have h1 : ∏ p ∈ B, p ≤ primorial (2 ^ (j + 1)) := by
    rw [primorial]
    refine Finset.prod_le_prod_of_subset_of_one_le' hsub ?_
    intro p hp _
    exact (Finset.mem_filter.mp hp).2.one_lt.le
  have h2 : primorial (2 ^ (j + 1)) ≤ 4 ^ (2 ^ (j + 1)) := primorial_le_4_pow _
  have h3 : (2 ^ j) ^ B.card ≤ ∏ p ∈ B, p := by
    calc (2 ^ j) ^ B.card = ∏ _p ∈ B, 2 ^ j := by rw [Finset.prod_const]
      _ ≤ ∏ p ∈ B, p := Finset.prod_le_prod' (fun p hp =>
          le_of_lt (Finset.mem_filter.mp hp).2.2)
  have h4 : (2 : ℕ) ^ (j * B.card) ≤ 2 ^ (2 ^ (j + 2)) := by
    calc (2 : ℕ) ^ (j * B.card) = (2 ^ j) ^ B.card := by rw [pow_mul]
      _ ≤ ∏ p ∈ B, p := h3
      _ ≤ 4 ^ (2 ^ (j + 1)) := le_trans h1 h2
      _ = 2 ^ (2 ^ (j + 2)) := by
          rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]
          congr 1
          ring
  have h5 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h4
  rw [Nat.mul_comm]
  exact h5

/-- Block bound: the sum of `1/p` over primes in `(2^j, 2^(j+1)]` is at most `4/j`. -/
lemma sum_inv_primes_block_le {j : ℕ} (hj : 1 ≤ j) :
    ∑ p ∈ (range (2 ^ (j + 1) + 1)).filter (fun p => Nat.Prime p ∧ 2 ^ j < p), (1 / (p : ℝ))
      ≤ 4 / j := by
  set B := (range (2 ^ (j + 1) + 1)).filter (fun p => Nat.Prime p ∧ 2 ^ j < p) with hB
  have hjR : (0 : ℝ) < (j : ℝ) := by exact_mod_cast hj
  have h1 : ∑ p ∈ B, (1 / (p : ℝ)) ≤ ∑ _p ∈ B, (1 / (2 ^ j : ℝ)) := by
    refine Finset.sum_le_sum (fun p hp => ?_)
    have hp2 : 2 ^ j < p := (Finset.mem_filter.mp hp).2.2
    have hpR : ((2 : ℝ) ^ j) ≤ (p : ℝ) := by
      have : ((2 ^ j : ℕ) : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp2.le
      simpa using this
    exact one_div_le_one_div_of_le (by positivity) hpR
  rw [Finset.sum_const, nsmul_eq_mul] at h1
  have hcard := card_primes_block_mul_le j
  have hcardR : (B.card : ℝ) * (j : ℝ) ≤ (2 : ℝ) ^ (j + 2) := by
    have : ((B.card * j : ℕ) : ℝ) ≤ ((2 ^ (j + 2) : ℕ) : ℝ) := by exact_mod_cast hcard
    push_cast at this
    linarith
  have h2 : (B.card : ℝ) * (1 / (2 ^ j : ℝ)) ≤ 4 / j := by
    rw [mul_one_div, div_le_div_iff₀ (by positivity) hjR]
    have : (2 : ℝ) ^ (j + 2) = 4 * 2 ^ j := by ring
    nlinarith [hcardR]
  linarith

/-- `∑_{p ≤ 2^q} 1/p ≤ 5 + 4 log q`. -/
lemma sum_inv_primesBelow_pow_two_step (q : ℕ) (hq : 1 ≤ q) :
    ∑ p ∈ Nat.primesBelow (2 ^ (q + 1) + 1), (1 / (p : ℝ))
      ≤ (∑ p ∈ Nat.primesBelow (2 ^ q + 1), (1 / (p : ℝ))) + 4 / q := by
  have hsplit := Finset.sum_filter_add_sum_filter_not (Nat.primesBelow (2 ^ (q + 1) + 1))
    (fun p => p ≤ 2 ^ q) (fun p => (1 / (p : ℝ)))
  have hlow : (Nat.primesBelow (2 ^ (q + 1) + 1)).filter (fun p => p ≤ 2 ^ q)
      = Nat.primesBelow (2 ^ q + 1) := by
    ext p
    simp only [Nat.primesBelow, Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨⟨_, hp⟩, hle⟩
      exact ⟨by omega, hp⟩
    · rintro ⟨hlt, hp⟩
      have : 2 ^ q ≤ 2 ^ (q + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      exact ⟨⟨by omega, hp⟩, by omega⟩
  have hhigh : (Nat.primesBelow (2 ^ (q + 1) + 1)).filter (fun p => ¬ p ≤ 2 ^ q)
      = (range (2 ^ (q + 1) + 1)).filter (fun p => Nat.Prime p ∧ 2 ^ q < p) := by
    ext p
    simp only [Nat.primesBelow, Finset.mem_filter, Finset.mem_range, not_le]
    tauto
  rw [hlow, hhigh] at hsplit
  have hblock := sum_inv_primes_block_le hq
  linarith

/-- `∑_{p ≤ 2^q} 1/p ≤ 5 + 4 log q`. -/
lemma sum_inv_primesBelow_pow_two_le {q : ℕ} (hq : 1 ≤ q) :
    ∑ p ∈ Nat.primesBelow (2 ^ q + 1), (1 / (p : ℝ)) ≤ 5 + 4 * Real.log q := by
  have key : ∀ r : ℕ, 1 ≤ r →
      ∑ p ∈ Nat.primesBelow (2 ^ r + 1), (1 / (p : ℝ))
        ≤ 1 / 2 + 4 * ((harmonic (r - 1) : ℚ) : ℝ) := by
    intro r hr
    induction r with
    | zero => omega
    | succ r ih =>
        rcases Nat.eq_zero_or_pos r with rfl | hr1
        · norm_num
          rw [show Nat.primesBelow 3 = {2} by decide]
          norm_num
        · have hstep := sum_inv_primesBelow_pow_two_step r hr1
          have hih := ih hr1
          have hharm : ((harmonic r : ℚ) : ℝ)
              = ((harmonic (r - 1) : ℚ) : ℝ) + 1 / (r : ℝ) := by
            obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
            simp only [Nat.add_sub_cancel]
            rw [harmonic_succ]
            push_cast
            ring
          simp only [Nat.add_sub_cancel]
          rw [hharm]
          have : (4 : ℝ) / r = 4 * (1 / (r : ℝ)) := by ring
          linarith [hstep, hih, this]
  have hkey := key q hq
  have hbound : ((harmonic (q - 1) : ℚ) : ℝ) ≤ 1 + Real.log q := by
    have h1 := harmonic_le_one_add_log (q - 1)
    have h2 : Real.log ((q - 1 : ℕ) : ℝ) ≤ Real.log q := by
      rcases Nat.eq_zero_or_pos (q - 1) with h | h
      · rw [h]
        simp only [Nat.cast_zero, Real.log_zero]
        exact Real.log_nonneg (by exact_mod_cast hq)
      · apply Real.log_le_log (by exact_mod_cast h)
        have : (q - 1 : ℕ) ≤ q := by omega
        exact_mod_cast this
    linarith
  linarith

/-! ### The two products appearing in the sieve -/

lemma oddPrimesLe_subset_primesBelow (z : ℕ) : oddPrimesLe z ⊆ Nat.primesBelow (z + 1) := by
  intro p hp
  rw [mem_oddPrimesLe] at hp
  rw [Nat.primesBelow, Finset.mem_filter, Finset.mem_range]
  exact ⟨by omega, hp.2.1⟩

lemma oddPrimesLe_eq_erase (z : ℕ) :
    oddPrimesLe z = (Nat.primesBelow (z + 1)).erase 2 := by
  ext p
  rw [mem_oddPrimesLe, Finset.mem_erase, Nat.primesBelow, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨hle, hp, hne⟩
    exact ⟨hne, by omega, hp⟩
  · rintro ⟨hne, hlt, hp⟩
    exact ⟨by omega, hp, hne⟩

/-- The main term of the sieve: `∏_{3 ≤ p ≤ z} (1 - 2/p) ≤ 4 e² / (log z)²`. -/
lemma prod_oddPrimesLe_one_sub_two_div_le {z : ℕ} (hz : 3 ≤ z) :
    ∏ p ∈ oddPrimesLe z, (1 - 2 / (p : ℝ)) ≤ 4 * Real.exp 1 ^ 2 / (Real.log z) ^ 2 := by
  have hzR : (3 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz
  have hlog : 1 < Real.log z := by
    have h3 : 1 < Real.log 3 := by
      have hlt : Real.log (Real.exp 1) < Real.log 3 :=
        Real.log_lt_log (Real.exp_pos 1) (by linarith [Real.exp_one_lt_d9])
      rwa [Real.log_exp] at hlt
    have : Real.log 3 ≤ Real.log z := Real.log_le_log (by norm_num) hzR
    linarith
  -- termwise bound
  have hterm : ∏ p ∈ oddPrimesLe z, (1 - 2 / (p : ℝ))
      ≤ ∏ p ∈ oddPrimesLe z, (1 - 1 / (p : ℝ)) ^ 2 := by
    refine Finset.prod_le_prod (fun p hp => ?_) (fun p hp => ?_)
    · have h3 : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast oddPrimesLe_three_le hp
      have : 2 / (p : ℝ) ≤ 2 / 3 := by
        apply div_le_div_of_nonneg_left (by norm_num) (by norm_num) h3
      linarith
    · have h3 : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast oddPrimesLe_three_le hp
      have hppos : (0 : ℝ) < (p : ℝ) := by linarith
      have : (1 - 1 / (p : ℝ)) ^ 2 - (1 - 2 / (p : ℝ)) = (1 / (p : ℝ)) ^ 2 := by
        field_simp
        ring
      nlinarith [sq_nonneg (1 / (p : ℝ))]
  -- relate to the full product over primes
  have h2mem : (2 : ℕ) ∈ Nat.primesBelow (z + 1) := by
    rw [Nat.primesBelow, Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, Nat.prime_two⟩
  have hsplit : ∏ p ∈ Nat.primesBelow (z + 1), (1 - 1 / (p : ℝ))
      = (1 - 1 / (2 : ℝ)) * ∏ p ∈ oddPrimesLe z, (1 - 1 / (p : ℝ)) := by
    have h := Finset.mul_prod_erase (Nat.primesBelow (z + 1)) (fun p : ℕ => 1 - 1 / (p : ℝ)) h2mem
    rw [← oddPrimesLe_eq_erase z] at h
    rw [← h]
    norm_num
  have hall := prod_primesBelow_one_sub_inv_le hz
  have hodd : ∏ p ∈ oddPrimesLe z, (1 - 1 / (p : ℝ)) ≤ 2 * (Real.exp 1 / Real.log z) := by
    rw [hsplit] at hall
    norm_num at hall ⊢
    linarith
  have hoddnonneg : 0 ≤ ∏ p ∈ oddPrimesLe z, (1 - 1 / (p : ℝ)) := by
    refine Finset.prod_nonneg (fun p hp => ?_)
    have h3 : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast oddPrimesLe_three_le hp
    have : 1 / (p : ℝ) ≤ 1 / 3 := one_div_le_one_div_of_le (by norm_num) h3
    linarith
  have hsq : ∏ p ∈ oddPrimesLe z, (1 - 1 / (p : ℝ)) ^ 2
      = (∏ p ∈ oddPrimesLe z, (1 - 1 / (p : ℝ))) ^ 2 := by
    rw [Finset.prod_pow]
  rw [hsq] at hterm
  have hfinal : (∏ p ∈ oddPrimesLe z, (1 - 1 / (p : ℝ))) ^ 2
      ≤ (2 * (Real.exp 1 / Real.log z)) ^ 2 := by
    apply pow_le_pow_left₀ hoddnonneg hodd
  have hexp : (2 * (Real.exp 1 / Real.log z)) ^ 2 = 4 * Real.exp 1 ^ 2 / (Real.log z) ^ 2 := by
    field_simp
    ring
  linarith [hterm, hfinal, hexp.le, hexp.ge]

/-- The tail term of the sieve: `∏_{3 ≤ p ≤ 2^q} (1 + 4/p) ≤ e^20 q^16`. -/
lemma prod_oddPrimesLe_one_add_four_div_le {q : ℕ} (hq : 1 ≤ q) :
    ∏ p ∈ oddPrimesLe (2 ^ q), (1 + 4 / (p : ℝ)) ≤ Real.exp 20 * (q : ℝ) ^ 16 := by
  have hqR : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have h1 : ∏ p ∈ oddPrimesLe (2 ^ q), (1 + 4 / (p : ℝ))
      ≤ ∏ p ∈ oddPrimesLe (2 ^ q), Real.exp (4 / (p : ℝ)) := by
    refine Finset.prod_le_prod (fun p hp => ?_) (fun p hp => ?_)
    · have h3 : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast oddPrimesLe_three_le hp
      positivity
    · have := Real.add_one_le_exp (4 / (p : ℝ))
      linarith
  rw [← Real.exp_sum] at h1
  have h2 : ∑ p ∈ oddPrimesLe (2 ^ q), (4 / (p : ℝ))
      ≤ 4 * ∑ p ∈ Nat.primesBelow (2 ^ q + 1), (1 / (p : ℝ)) := by
    rw [Finset.mul_sum]
    have hsub : ∑ p ∈ oddPrimesLe (2 ^ q), (4 * (1 / (p : ℝ)))
        ≤ ∑ p ∈ Nat.primesBelow (2 ^ q + 1), (4 * (1 / (p : ℝ))) := by
      refine Finset.sum_le_sum_of_subset_of_nonneg (oddPrimesLe_subset_primesBelow _) ?_
      intro p hp _
      have hp2 : 2 ≤ p := (Nat.prime_of_mem_primesBelow hp).two_le
      have : (0 : ℝ) < (p : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_two hp2
      positivity
    calc ∑ p ∈ oddPrimesLe (2 ^ q), (4 / (p : ℝ))
        = ∑ p ∈ oddPrimesLe (2 ^ q), (4 * (1 / (p : ℝ))) := by
          refine Finset.sum_congr rfl (fun p _ => by ring)
      _ ≤ _ := hsub
  have h3 := sum_inv_primesBelow_pow_two_le hq
  have h4 : ∑ p ∈ oddPrimesLe (2 ^ q), (4 / (p : ℝ)) ≤ 20 + 16 * Real.log q := by
    linarith
  have h5 : Real.exp (∑ p ∈ oddPrimesLe (2 ^ q), (4 / (p : ℝ))) ≤ Real.exp (20 + 16 * Real.log q) :=
    Real.exp_le_exp.mpr h4
  have h6 : Real.exp (20 + 16 * Real.log q) = Real.exp 20 * (q : ℝ) ^ 16 := by
    rw [Real.exp_add]
    congr 1
    rw [show (16 : ℝ) * Real.log q = Real.log ((q : ℝ) ^ 16) by
      rw [Real.log_pow]; push_cast; ring]
    exact Real.exp_log (by positivity)
  linarith [h1, h5, h6.le, h6.ge]

end Brun

import Mathlib

/-!
# Definitions for Brun's theorem

Basic counting functions used in the proof that the sum of reciprocals of twin primes
converges.
-/

namespace Brun

open Finset

/-- The odd primes `≤ z`. -/
def oddPrimesLe (z : ℕ) : Finset ℕ :=
  (range (z + 1)).filter (fun p => Nat.Prime p ∧ p ≠ 2)

/-- The number of `n < N` such that both `n` and `n + 2` are prime. -/
def twinCount (N : ℕ) : ℕ :=
  ((range N).filter (fun n => Nat.Prime n ∧ Nat.Prime (n + 2))).card

/-- The number of `n < N` such that `n * (n + 2)` has no odd prime factor `≤ z`. -/
def siftCount (N z : ℕ) : ℕ :=
  ((range N).filter (fun n => ∀ p ∈ oddPrimesLe z, ¬ p ∣ n * (n + 2))).card

/-- The number of `n < N` such that every `p ∈ S` divides `n * (n + 2)`. -/
def dvdCount (N : ℕ) (S : Finset ℕ) : ℕ :=
  ((range N).filter (fun n => ∀ p ∈ S, p ∣ n * (n + 2))).card

lemma mem_oddPrimesLe {z p : ℕ} : p ∈ oddPrimesLe z ↔ p ≤ z ∧ Nat.Prime p ∧ p ≠ 2 := by
  simp [oddPrimesLe, Nat.lt_succ_iff, and_assoc]

lemma oddPrimesLe_prime {z p : ℕ} (hp : p ∈ oddPrimesLe z) : Nat.Prime p :=
  (mem_oddPrimesLe.mp hp).2.1

lemma oddPrimesLe_ne_two {z p : ℕ} (hp : p ∈ oddPrimesLe z) : p ≠ 2 :=
  (mem_oddPrimesLe.mp hp).2.2

lemma oddPrimesLe_three_le {z p : ℕ} (hp : p ∈ oddPrimesLe z) : 3 ≤ p := by
  have h2 := (oddPrimesLe_prime hp).two_le
  have h3 := oddPrimesLe_ne_two hp
  omega

end Brun

import RequestProject.Brun.Counting
import RequestProject.Brun.Bonferroni
import RequestProject.Brun.PrimeSums

/-!
# Brun's sieve

The main result is `Brun.twinCount_le`, an explicit upper bound for the number of `n < N`
such that `n` and `n + 2` are both prime, in terms of a sieve level `z` and an even
truncation level `k`.
-/

namespace Brun

open Finset

/-! ### Alternating sums over subsets -/

lemma prod_one_add_eq_sum_powerset (P : Finset ℕ) (a : ℕ → ℝ) :
    ∏ p ∈ P, (1 + a p) = ∑ S ∈ P.powerset, ∏ p ∈ S, a p := by
  have := Finset.prod_add a (fun _ => (1 : ℝ)) P
  simp only [Finset.prod_const_one, mul_one] at this
  rw [← this]
  exact Finset.prod_congr rfl (fun p _ => by ring)

lemma sum_powerset_eq_sum_range (P : Finset ℕ) (g : Finset ℕ → ℝ) {R : ℕ}
    (hR : P.card + 1 ≤ R) :
    ∑ S ∈ P.powerset, g S = ∑ j ∈ range R, ∑ S ∈ P.powersetCard j, g S := by
  rw [Finset.sum_powerset]
  refine Finset.sum_subset (by simpa using hR) ?_
  intro j _ hj
  simp only [Finset.mem_range, not_lt] at hj
  rw [Finset.powersetCard_eq_empty.mpr (by omega)]
  simp

/-- Truncated inclusion–exclusion for a product `∏ (1 - a p)`. -/
lemma truncated_alt_sum_le (P : Finset ℕ) (a : ℕ → ℝ) (ha : ∀ p ∈ P, 0 ≤ a p) (k : ℕ) :
    ∑ j ∈ range (k + 1), (-1 : ℝ) ^ j * ∑ S ∈ P.powersetCard j, ∏ p ∈ S, a p
      ≤ ∏ p ∈ P, (1 - a p) + (∏ p ∈ P, (1 + 2 * a p)) / 2 ^ (k + 1) := by
  classical
  set R := max (k + 1) (P.card + 1) with hR
  have hkR : k + 1 ≤ R := le_max_left _ _
  have hPR : P.card + 1 ≤ R := le_max_right _ _
  -- the full alternating sum is the product
  have hfull : ∑ j ∈ range R, (-1 : ℝ) ^ j * ∑ S ∈ P.powersetCard j, ∏ p ∈ S, a p
      = ∏ p ∈ P, (1 - a p) := by
    have h1 : ∏ p ∈ P, (1 - a p) = ∑ S ∈ P.powerset, ∏ p ∈ S, (-(a p)) := by
      have := prod_one_add_eq_sum_powerset P (fun p => -(a p))
      simpa using this
    rw [h1, sum_powerset_eq_sum_range P (fun S => ∏ p ∈ S, (-(a p))) hPR]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun S hS => ?_)
    have hcard : S.card = j := (Finset.mem_powersetCard.mp hS).2
    rw [Finset.prod_neg, hcard]
  -- split off the tail
  have hsplit : ∑ j ∈ range R, (-1 : ℝ) ^ j * ∑ S ∈ P.powersetCard j, ∏ p ∈ S, a p
      = (∑ j ∈ range (k + 1), (-1 : ℝ) ^ j * ∑ S ∈ P.powersetCard j, ∏ p ∈ S, a p)
        + ∑ j ∈ Ico (k + 1) R, (-1 : ℝ) ^ j * ∑ S ∈ P.powersetCard j, ∏ p ∈ S, a p := by
    rw [Finset.range_eq_Ico, ← Finset.sum_Ico_consecutive _ (Nat.zero_le (k + 1)) hkR]
  have hnn : ∀ j, ∀ S ∈ P.powersetCard j, 0 ≤ ∏ p ∈ S, a p := by
    intro j S hS
    refine Finset.prod_nonneg (fun p hp => ha p ?_)
    exact (Finset.mem_powersetCard.mp hS).1 hp
  -- bound the tail
  have htail : -(∑ j ∈ Ico (k + 1) R, (-1 : ℝ) ^ j * ∑ S ∈ P.powersetCard j, ∏ p ∈ S, a p)
      ≤ (∏ p ∈ P, (1 + 2 * a p)) / 2 ^ (k + 1) := by
    have h1 : -(∑ j ∈ Ico (k + 1) R, (-1 : ℝ) ^ j * ∑ S ∈ P.powersetCard j, ∏ p ∈ S, a p)
        ≤ ∑ j ∈ Ico (k + 1) R, ∑ S ∈ P.powersetCard j, ∏ p ∈ S, a p := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_le_sum (fun j _ => ?_)
      have hs : 0 ≤ ∑ S ∈ P.powersetCard j, ∏ p ∈ S, a p :=
        Finset.sum_nonneg (hnn j)
      rcases Nat.even_or_odd j with hj | hj
      · rw [hj.neg_one_pow]
        linarith
      · rw [hj.neg_one_pow]
        linarith
    have h2 : ∑ j ∈ Ico (k + 1) R, ∑ S ∈ P.powersetCard j, ∏ p ∈ S, a p
        ≤ ∑ j ∈ Ico (k + 1) R, ∑ S ∈ P.powersetCard j, (∏ p ∈ S, (2 * a p)) / 2 ^ (k + 1) := by
      refine Finset.sum_le_sum (fun j hj => Finset.sum_le_sum (fun S hS => ?_))
      simp only [Finset.mem_Ico] at hj
      have hcard : S.card = j := (Finset.mem_powersetCard.mp hS).2
      have hprod : ∏ p ∈ S, (2 * a p) = 2 ^ S.card * ∏ p ∈ S, a p := by
        rw [Finset.prod_mul_distrib, Finset.prod_const]
      rw [hprod, hcard]
      have hnn' : 0 ≤ ∏ p ∈ S, a p := hnn j S hS
      rw [le_div_iff₀ (by positivity)]
      have : (2 : ℝ) ^ (k + 1) ≤ 2 ^ j := by
        apply pow_le_pow_right₀ (by norm_num) hj.1
      nlinarith
    have h3 : ∑ j ∈ Ico (k + 1) R, ∑ S ∈ P.powersetCard j, (∏ p ∈ S, (2 * a p)) / 2 ^ (k + 1)
        ≤ ∑ j ∈ range R, ∑ S ∈ P.powersetCard j, (∏ p ∈ S, (2 * a p)) / 2 ^ (k + 1) := by
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
      · intro j hj
        simp only [Finset.mem_Ico] at hj
        simp only [Finset.mem_range]
        omega
      · intro j _ _
        refine Finset.sum_nonneg (fun S hS => ?_)
        have : 0 ≤ ∏ p ∈ S, (2 * a p) := by
          refine Finset.prod_nonneg (fun p hp => ?_)
          have := ha p ((Finset.mem_powersetCard.mp hS).1 hp)
          linarith
        positivity
    have h4 : ∑ j ∈ range R, ∑ S ∈ P.powersetCard j, (∏ p ∈ S, (2 * a p)) / 2 ^ (k + 1)
        = (∏ p ∈ P, (1 + 2 * a p)) / 2 ^ (k + 1) := by
      rw [prod_one_add_eq_sum_powerset P (fun p => 2 * a p),
        sum_powerset_eq_sum_range P (fun S => ∏ p ∈ S, (2 * a p)) hPR, Finset.sum_div]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [Finset.sum_div]
    linarith
  linarith [hfull, hsplit, htail]

/-! ### The sieve bound -/

lemma twinCount_le_siftCount (N z : ℕ) : twinCount N ≤ (z + 1) + siftCount N z := by
  have hsub : (range N).filter (fun n => Nat.Prime n ∧ Nat.Prime (n + 2))
      ⊆ (range (z + 1)) ∪ ((range N).filter (fun n => ∀ p ∈ oddPrimesLe z, ¬ p ∣ n * (n + 2))) := by
    intro n hn
    simp only [Finset.mem_filter, Finset.mem_range] at hn
    obtain ⟨hnN, hn1, hn2⟩ := hn
    rw [Finset.mem_union]
    by_cases hz : n ≤ z
    · left; simp only [Finset.mem_range]; omega
    · right
      simp only [Finset.mem_filter, Finset.mem_range]
      refine ⟨hnN, fun p hp hdvd => ?_⟩
      obtain ⟨hple, hpp, _⟩ := mem_oddPrimesLe.mp hp
      rcases hpp.dvd_mul.mp hdvd with h | h
      · have := (Nat.prime_dvd_prime_iff_eq hpp hn1).mp h
        omega
      · have := (Nat.prime_dvd_prime_iff_eq hpp hn2).mp h
        omega
  calc twinCount N ≤ ((range (z + 1)) ∪ ((range N).filter
        (fun n => ∀ p ∈ oddPrimesLe z, ¬ p ∣ n * (n + 2)))).card := Finset.card_le_card hsub
    _ ≤ (range (z + 1)).card + ((range N).filter
        (fun n => ∀ p ∈ oddPrimesLe z, ¬ p ∣ n * (n + 2))).card := Finset.card_union_le _ _
    _ = (z + 1) + siftCount N z := by rw [Finset.card_range]; rfl

lemma siftCount_le_bonferroni (N z k : ℕ) (hk : Even k) :
    (siftCount N z : ℝ)
      ≤ ∑ j ∈ range (k + 1), (-1 : ℝ) ^ j *
          ∑ S ∈ (oddPrimesLe z).powersetCard j, (dvdCount N S : ℝ) := by
  have hcard : (siftCount N z : ℝ)
      = ∑ n ∈ range N, (if ∀ p ∈ oddPrimesLe z, ¬ p ∣ n * (n + 2) then (1 : ℝ) else 0) := by
    rw [siftCount, Finset.card_filter]
    push_cast
    rfl
  rw [hcard]
  have hstep : ∀ n ∈ range N,
      (if ∀ p ∈ oddPrimesLe z, ¬ p ∣ n * (n + 2) then (1 : ℝ) else 0)
        ≤ ∑ j ∈ range (k + 1), (-1 : ℝ) ^ j *
            (((oddPrimesLe z).powersetCard j).filter
              (fun S => ∀ p ∈ S, p ∣ n * (n + 2))).card := by
    intro n _
    exact bonferroni_sets (oddPrimesLe z) (fun p => p ∣ n * (n + 2)) k hk
  refine le_trans (Finset.sum_le_sum hstep) ?_
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum (fun j _ => ?_)
  rw [← Finset.mul_sum]
  refine le_of_eq ?_
  congr 1
  -- double counting
  have hdc : ∀ n : ℕ, ((((oddPrimesLe z).powersetCard j).filter
        (fun S => ∀ p ∈ S, p ∣ n * (n + 2))).card : ℝ)
      = ∑ S ∈ (oddPrimesLe z).powersetCard j,
          (if (∀ p ∈ S, p ∣ n * (n + 2)) then (1 : ℝ) else 0) := by
    intro n
    rw [Finset.card_filter]
    push_cast
    rfl
  simp only [hdc]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun S _ => ?_)
  rw [dvdCount, Finset.card_filter]
  push_cast
  rfl

/-- The main sieve estimate. -/
theorem siftCount_le (N z k : ℕ) (hk : Even k) :
    (siftCount N z : ℝ)
      ≤ (N : ℝ) * (∏ p ∈ oddPrimesLe z, (1 - 2 / (p : ℝ)))
        + (N : ℝ) * (∏ p ∈ oddPrimesLe z, (1 + 4 / (p : ℝ))) / 2 ^ (k + 1)
        + (k + 1) * (2 * z + 3) ^ k := by
  set P := oddPrimesLe z with hP
  have hprim : ∀ S ∈ P.powerset, ∀ p ∈ S, Nat.Prime p ∧ p ≠ 2 := by
    intro S hS p hp
    have := (Finset.mem_powerset.mp hS) hp
    exact ⟨oddPrimesLe_prime this, oddPrimesLe_ne_two this⟩
  -- the "main term" of each `dvdCount`
  have hm : ∀ S : Finset ℕ, (∀ p ∈ S, Nat.Prime p ∧ p ≠ 2) →
      2 ^ S.card * (N : ℝ) / (∏ p ∈ S, (p : ℝ)) = (N : ℝ) * ∏ p ∈ S, (2 / (p : ℝ)) := by
    intro S hS
    have hpos : (0 : ℝ) < ∏ p ∈ S, (p : ℝ) :=
      Finset.prod_pos (fun p hp => by exact_mod_cast (hS p hp).1.pos)
    rw [Finset.prod_div_distrib, Finset.prod_const]
    field_simp
  have hbound : ∀ j, ∀ S ∈ P.powersetCard j,
      |(dvdCount N S : ℝ) - (N : ℝ) * ∏ p ∈ S, (2 / (p : ℝ))| ≤ 2 ^ j := by
    intro j S hS
    have hSP : S ⊆ P := (Finset.mem_powersetCard.mp hS).1
    have hcard : S.card = j := (Finset.mem_powersetCard.mp hS).2
    have hprimS : ∀ p ∈ S, Nat.Prime p ∧ p ≠ 2 := fun p hp =>
      ⟨oddPrimesLe_prime (hSP hp), oddPrimesLe_ne_two (hSP hp)⟩
    have := abs_dvdCount_sub_le N S hprimS
    rwa [hm S hprimS, hcard] at this
  -- split into main term and error
  have hsplit : ∑ j ∈ range (k + 1), (-1 : ℝ) ^ j * ∑ S ∈ P.powersetCard j, (dvdCount N S : ℝ)
      = (∑ j ∈ range (k + 1), (-1 : ℝ) ^ j *
            ∑ S ∈ P.powersetCard j, ((N : ℝ) * ∏ p ∈ S, (2 / (p : ℝ))))
        + ∑ j ∈ range (k + 1), (-1 : ℝ) ^ j *
            ∑ S ∈ P.powersetCard j, ((dvdCount N S : ℝ) - (N : ℝ) * ∏ p ∈ S, (2 / (p : ℝ))) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [← mul_add, ← Finset.sum_add_distrib]
    congr 1
    exact Finset.sum_congr rfl (fun S _ => by ring)
  -- bound the error
  have herr : ∑ j ∈ range (k + 1), (-1 : ℝ) ^ j *
      ∑ S ∈ P.powersetCard j, ((dvdCount N S : ℝ) - (N : ℝ) * ∏ p ∈ S, (2 / (p : ℝ)))
        ≤ (k + 1) * (2 * z + 3) ^ k := by
    have h1 : |∑ j ∈ range (k + 1), (-1 : ℝ) ^ j *
        ∑ S ∈ P.powersetCard j, ((dvdCount N S : ℝ) - (N : ℝ) * ∏ p ∈ S, (2 / (p : ℝ)))|
          ≤ ∑ j ∈ range (k + 1), ((P.card.choose j : ℝ) * 2 ^ j) := by
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum (fun j _ => ?_))
      rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
      refine le_trans (Finset.sum_le_sum (fun S hS => hbound j S hS)) ?_
      rw [Finset.sum_const, Finset.card_powersetCard, nsmul_eq_mul]
    have h2 : ∀ j ∈ range (k + 1), ((P.card.choose j : ℝ) * 2 ^ j) ≤ (2 * z + 3) ^ k := by
      intro j hj
      simp only [Finset.mem_range] at hj
      have hPcard : P.card ≤ z + 1 := by
        have : P ⊆ range (z + 1) := by
          intro p hp
          simp only [Finset.mem_range]
          have := mem_oddPrimesLe.mp hp
          omega
        simpa using Finset.card_le_card this
      have hchoose : (P.card.choose j : ℝ) ≤ (P.card : ℝ) ^ j := by
        have := Nat.choose_le_pow P.card j
        exact_mod_cast this
      have hstep : ((P.card : ℝ)) * 2 ≤ 2 * z + 3 := by
        have : (P.card : ℝ) ≤ (z : ℝ) + 1 := by exact_mod_cast hPcard
        linarith
      calc (P.card.choose j : ℝ) * 2 ^ j ≤ (P.card : ℝ) ^ j * 2 ^ j := by
            have : (0 : ℝ) ≤ 2 ^ j := by positivity
            nlinarith [hchoose]
        _ = ((P.card : ℝ) * 2) ^ j := by rw [mul_pow]
        _ ≤ (2 * z + 3) ^ j := by
            apply pow_le_pow_left₀ (by positivity) hstep
        _ ≤ (2 * z + 3) ^ k := by
            refine pow_le_pow_right₀ ?_ (by omega)
            have : (0 : ℝ) ≤ (z : ℝ) := Nat.cast_nonneg z
            linarith
    have h3 : ∑ j ∈ range (k + 1), ((P.card.choose j : ℝ) * 2 ^ j) ≤ (k + 1) * (2 * z + 3) ^ k := by
      calc ∑ j ∈ range (k + 1), ((P.card.choose j : ℝ) * 2 ^ j)
          ≤ ∑ _j ∈ range (k + 1), ((2 * z + 3 : ℝ) ^ k) := Finset.sum_le_sum h2
        _ = (k + 1) * (2 * z + 3) ^ k := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
            push_cast
            ring
    calc _ ≤ |∑ j ∈ range (k + 1), (-1 : ℝ) ^ j *
        ∑ S ∈ P.powersetCard j, ((dvdCount N S : ℝ) - (N : ℝ) * ∏ p ∈ S, (2 / (p : ℝ)))| :=
          le_abs_self _
      _ ≤ _ := le_trans h1 h3
  -- bound the main term
  have hmain : ∑ j ∈ range (k + 1), (-1 : ℝ) ^ j *
      ∑ S ∈ P.powersetCard j, ((N : ℝ) * ∏ p ∈ S, (2 / (p : ℝ)))
        ≤ (N : ℝ) * (∏ p ∈ P, (1 - 2 / (p : ℝ)))
          + (N : ℝ) * (∏ p ∈ P, (1 + 4 / (p : ℝ))) / 2 ^ (k + 1) := by
    have hfac : ∑ j ∈ range (k + 1), (-1 : ℝ) ^ j *
        ∑ S ∈ P.powersetCard j, ((N : ℝ) * ∏ p ∈ S, (2 / (p : ℝ)))
          = (N : ℝ) * ∑ j ∈ range (k + 1), (-1 : ℝ) ^ j *
              ∑ S ∈ P.powersetCard j, ∏ p ∈ S, (2 / (p : ℝ)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [← Finset.mul_sum]
      ring
    rw [hfac]
    have ha : ∀ p ∈ P, (0 : ℝ) ≤ 2 / (p : ℝ) := by
      intro p hp
      have : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast oddPrimesLe_three_le hp
      positivity
    have := truncated_alt_sum_le P (fun p => 2 / (p : ℝ)) ha k
    have hNnn : (0 : ℝ) ≤ (N : ℝ) := by positivity
    have hmul := mul_le_mul_of_nonneg_left this hNnn
    have heq : ∏ p ∈ P, (1 + 2 * (2 / (p : ℝ))) = ∏ p ∈ P, (1 + 4 / (p : ℝ)) := by
      refine Finset.prod_congr rfl (fun p _ => by ring)
    rw [heq] at hmul
    calc (N : ℝ) * ∑ j ∈ range (k + 1), (-1 : ℝ) ^ j *
          ∑ S ∈ P.powersetCard j, ∏ p ∈ S, (2 / (p : ℝ))
        ≤ (N : ℝ) * ((∏ p ∈ P, (1 - 2 / (p : ℝ)))
            + (∏ p ∈ P, (1 + 4 / (p : ℝ))) / 2 ^ (k + 1)) := hmul
      _ = _ := by ring
  have := siftCount_le_bonferroni N z k hk
  rw [hsplit] at this
  linarith

/-- Brun's sieve bound for the twin prime counting function. -/
theorem twinCount_le (N z k : ℕ) (hk : Even k) :
    (twinCount N : ℝ)
      ≤ (z + 1) + (N : ℝ) * (∏ p ∈ oddPrimesLe z, (1 - 2 / (p : ℝ)))
        + (N : ℝ) * (∏ p ∈ oddPrimesLe z, (1 + 4 / (p : ℝ))) / 2 ^ (k + 1)
        + (k + 1) * (2 * z + 3) ^ k := by
  have h1 := twinCount_le_siftCount N z
  have h2 := siftCount_le N z k hk
  have h1R : (twinCount N : ℝ) ≤ (z + 1 : ℕ) + (siftCount N z : ℝ) := by exact_mod_cast h1
  push_cast at h1R
  linarith

end Brun

