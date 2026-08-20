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
