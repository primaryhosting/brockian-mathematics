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
# Brun Twin Reciprocal
Category: Frontier — Prime Numbers
Target: Frontier.Brun_twin_reciprocal
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 requires `import` lines to precede any module docstring `/-! ... -/`,
-- so the header above is written as an ordinary block comment.)

import RequestProject.Brun.Summable

/-!
# Brun Twin Reciprocal
Category: Frontier — Prime Numbers
Target: Frontier.Brun_twin_reciprocal
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-- **Brun's theorem**: the sum of the reciprocals of the twin primes converges.
Here the index type is the set of primes `p` such that `p + 2` is also prime. -/
theorem Frontier.Brun_twin_reciprocal :
    Summable (fun p : {p : ℕ // p.Prime ∧ (p + 2).Prime} => (1 : ℝ) / p) := by
  have h := Brun.summable_twin_indicator
  rw [← summable_subtype_iff_indicator] at h
  exact h

import RequestProject.Brun.Sieve

/-!
# Summability of the reciprocals of the twin primes

Choosing the sieve parameters `z = 2 ^ (N / (4 (k+1)))` and `k ≍ log N` in Brun's sieve bound
`Brun.twinCount_le` gives `twinCount (2 ^ (N+1)) ≪ 2 ^ N (log N)^2 / N^2`, which is summable
after dividing by `2 ^ N`. A dyadic decomposition then shows that the sum of the reciprocals
of the twin primes converges.
-/

open Finset Filter

namespace Brun

/-- A polynomial is eventually dominated by `2 ^ m`. -/
theorem exists_pow_bound (a b : ℕ) : ∃ m₀ : ℕ, ∀ m ≥ m₀, a * (m + 2) ^ b ≤ 2 ^ m := by
  have h : (fun n : ℕ => ((n : ℝ)) ^ b) =o[Filter.atTop] fun n : ℕ => (2:ℝ) ^ n :=
    isLittleO_pow_const_const_pow_of_one_lt b (by norm_num)
  have hc : (0:ℝ) < 1 / (4 * a + 4) := by positivity
  have h2 := h.def hc
  rw [Filter.eventually_atTop] at h2
  obtain ⟨m₁, hm₁⟩ := h2
  refine ⟨m₁, fun m hm => ?_⟩
  have hthis := hm₁ (m + 2) (by omega)
  simp only [Real.norm_eq_abs] at hthis
  have h3 : ((m:ℝ) + 2) ^ b ≤ 1 / (4 * a + 4) * (4 * 2 ^ m) := by
    calc ((m:ℝ) + 2) ^ b = |(((m + 2 : ℕ) : ℝ)) ^ b| := by
          rw [abs_of_nonneg (by positivity)]; push_cast; ring
      _ ≤ 1 / (4 * a + 4) * |(2:ℝ) ^ (m + 2)| := hthis
      _ = 1 / (4 * a + 4) * (4 * 2 ^ m) := by
          rw [abs_of_nonneg (by positivity)]; ring
  have ha : (0:ℝ) ≤ a := by positivity
  have hpos : (0:ℝ) < 4 * (a:ℝ) + 4 := by positivity
  have h2m : (0:ℝ) < (2:ℝ) ^ m := by positivity
  have h5 := mul_le_mul_of_nonneg_left h3 ha
  have key : (a:ℝ) * (1 / (4 * a + 4) * (4 * 2 ^ m)) = (4 * a * 2 ^ m) / (4 * a + 4) := by
    field_simp
  rw [key, le_div_iff₀ hpos] at h5
  have hgoal : (a : ℝ) * ((m:ℝ) + 2) ^ b ≤ 2 ^ m := by nlinarith
  have hcast : ((a * (m + 2) ^ b : ℕ) : ℝ) ≤ ((2 ^ m : ℕ) : ℝ) := by push_cast; linarith
  exact_mod_cast hcast

/-- Any fixed power of `log₂ N` is eventually at most `N`. -/
theorem exists_log_poly_bound (a b : ℕ) : ∃ N₀ : ℕ, ∀ N ≥ N₀, a * (Nat.log 2 N + 1) ^ b ≤ N := by
  obtain ⟨m₀, hm₀⟩ := exists_pow_bound a b
  refine ⟨2 ^ m₀, fun N hN => ?_⟩
  have hNpos : 0 < N := lt_of_lt_of_le (Nat.pow_pos (by norm_num)) hN
  set m := Nat.log 2 N with hm
  have hmm : m₀ ≤ m := Nat.le_log_of_pow_le (by norm_num) hN
  have h1 : a * (m + 1) ^ b ≤ a * (m + 2) ^ b :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) b)
  exact h1.trans ((hm₀ m hmm).trans (Nat.pow_log_le_self 2 hNpos.ne'))

/-- The final combination step in the dyadic block estimate: given the four bounds for the
terms of Brun's sieve inequality, the block bound follows. -/
lemma twinCount_block_combine (b N L M k A c₀ : ℕ) (C P D tc : ℝ) (hC : 0 < C)
    (hCle : C ≤ 2 ^ c₀) (hN1 : 1 ≤ N) (hLpos : 1 ≤ L) (hNL : N < 2 ^ L) (hMN : M ≤ N)
    (hM2 : 2 ≤ M) (hk : k = 2 * (c₀ + (A + 2) * L)) (hNbL : N ≤ 8 * (b * L * M))
    (hPb : P ≤ C * (Real.log ((2:ℝ) ^ M)) ^ A)
    (hD : D = (2:ℝ) ^ N / (N:ℝ) ^ 2)
    (hB1 : (2:ℝ) ^ M + 1 ≤ D) (hB4 : 2 * (2 * (2:ℝ) ^ M) ^ k ≤ D)
    (hmain : tc ≤ (2:ℝ) ^ M + 1
      + (2:ℝ) ^ (N + 1) * (4 / (Real.log ((2:ℝ) ^ M)) ^ 2 + (1/2) ^ k * P)
      + 2 * (2 * (2:ℝ) ^ M) ^ k) :
    tc ≤ (4 + 512 * (b:ℝ) ^ 2 / (Real.log 2) ^ 2) * (L:ℝ) ^ 2 / (N:ℝ) ^ 2 * (2:ℝ) ^ N := by
  have hn : (0:ℝ) < (N:ℝ) := by exact_mod_cast hN1
  have hDpos : 0 < D := by rw [hD]; positivity
  have hl : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hB2 : (2:ℝ) ^ (N + 1) * (4 / (Real.log ((2:ℝ) ^ M)) ^ 2)
      ≤ 512 * (b:ℝ) ^ 2 / (Real.log 2) ^ 2 * (L:ℝ) ^ 2 * D := by
    have hu : (0:ℝ) < (M:ℝ) := by exact_mod_cast (by omega : 0 < M)
    have hlogz : Real.log ((2:ℝ) ^ M) = (M:ℝ) * Real.log 2 := by rw [Real.log_pow]
    have hcast : (N:ℝ) ≤ 8 * ((b:ℝ) * L * M) := by exact_mod_cast hNbL
    have hkey : (8:ℝ) * (N:ℝ) ^ 2 ≤ 512 * (b:ℝ) ^ 2 * (L:ℝ) ^ 2 * (M:ℝ) ^ 2 := by
      nlinarith [hcast, hn.le, sq_nonneg ((b:ℝ) * L * M)]
    rw [hlogz, hD]
    have key2 : (2:ℝ) ^ (N + 1) * (4 / ((M:ℝ) * Real.log 2) ^ 2)
        = (8 * 2 ^ N) / ((M:ℝ) ^ 2 * (Real.log 2) ^ 2) := by field_simp; ring
    have key3 : 512 * (b:ℝ) ^ 2 / (Real.log 2) ^ 2 * (L:ℝ) ^ 2 * ((2:ℝ) ^ N / (N:ℝ) ^ 2)
        = (512 * (b:ℝ) ^ 2 * (L:ℝ) ^ 2 * 2 ^ N) / ((Real.log 2) ^ 2 * (N:ℝ) ^ 2) := by field_simp
    rw [key2, key3, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_right hkey
      (by positivity : (0:ℝ) ≤ (2:ℝ) ^ N * (Real.log 2) ^ 2)]
  have hB3 : (2:ℝ) ^ (N + 1) * ((1/2) ^ k * P) ≤ 2 * D := by
    have hsmall : (1/2 : ℝ) ^ k * P ≤ 1 / (N:ℝ) ^ 2 := by
      have hl2 : Real.log 2 ≤ 1 := by
        have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 by norm_num)
        linarith
      have hlogz0 : (0:ℝ) ≤ Real.log ((2:ℝ) ^ M) := by rw [Real.log_pow]; positivity
      have hlogzN : Real.log ((2:ℝ) ^ M) ≤ (N:ℝ) := by
        rw [Real.log_pow]
        have hMN' : (M:ℝ) ≤ (N:ℝ) := by exact_mod_cast hMN
        nlinarith [Nat.cast_nonneg (α := ℝ) M]
      have hPN : P ≤ C * (N:ℝ) ^ A := hPb.trans (by gcongr)
      have hNL' : (N:ℝ) ≤ (2:ℝ) ^ L := by exact_mod_cast hNL.le
      have h2k : C * (N:ℝ) ^ (A + 2) ≤ (2:ℝ) ^ k := by
        have e1 : (2:ℝ) ^ (c₀ + (A + 2) * L) ≤ 2 ^ k :=
          pow_le_pow_right₀ (by norm_num) (by omega)
        have e2 : (2:ℝ) ^ (c₀ + (A + 2) * L) = 2 ^ c₀ * ((2:ℝ) ^ L) ^ (A + 2) := by
          rw [pow_add, ← pow_mul, Nat.mul_comm]
        have e3 : C * (N:ℝ) ^ (A + 2) ≤ 2 ^ c₀ * ((2:ℝ) ^ L) ^ (A + 2) := by gcongr
        linarith [e2 ▸ e1]
      have hfrac : (1/2:ℝ) ^ k * P = P / 2 ^ k := by rw [div_pow, one_pow]; ring
      have hquot : C * (N:ℝ) ^ A / (C * (N:ℝ) ^ (A + 2)) = 1 / (N:ℝ) ^ 2 := by
        rw [pow_add]; field_simp
      rw [hfrac, ← hquot]
      exact div_le_div₀ (by positivity) hPN (by positivity) h2k
    have h2N1 : (2:ℝ) ^ (N + 1) = 2 * 2 ^ N := by rw [pow_succ]; ring
    calc (2:ℝ) ^ (N + 1) * ((1/2) ^ k * P) ≤ (2:ℝ) ^ (N + 1) * (1 / (N:ℝ) ^ 2) := by gcongr
      _ = 2 * D := by rw [hD, h2N1]; ring
  have hLsq : (1:ℝ) ≤ (L:ℝ) ^ 2 := by
    have : (1:ℝ) ≤ (L:ℝ) := by exact_mod_cast hLpos
    nlinarith
  have hSnn : (0:ℝ) ≤ 512 * (b:ℝ) ^ 2 / (Real.log 2) ^ 2 := by positivity
  have hgoal_eq : (4 + 512 * (b:ℝ) ^ 2 / (Real.log 2) ^ 2) * (L:ℝ) ^ 2 / (N:ℝ) ^ 2 * (2:ℝ) ^ N
      = (4 + 512 * (b:ℝ) ^ 2 / (Real.log 2) ^ 2) * (L:ℝ) ^ 2 * D := by rw [hD]; ring
  rw [hgoal_eq]
  have hsplit : (2:ℝ) ^ (N + 1) * (4 / (Real.log ((2:ℝ) ^ M)) ^ 2 + (1/2) ^ k * P)
      = (2:ℝ) ^ (N + 1) * (4 / (Real.log ((2:ℝ) ^ M)) ^ 2)
        + (2:ℝ) ^ (N + 1) * ((1/2) ^ k * P) := by ring
  rw [hsplit] at hmain
  nlinarith [hmain, hB1, hB2, hB3, hB4, hDpos, hLsq, hSnn,
    mul_nonneg hSnn hDpos.le, mul_le_mul_of_nonneg_right hLsq hDpos.le]

/-- Brun's bound, with the sieve parameters chosen: the number of twin primes up to `2^(N+1)`
is `O(2^N (log N)^2 / N^2)`. -/
theorem exists_twinCount_block_bound :
    ∃ (c : ℝ) (N₀ : ℕ), ∀ N, N₀ ≤ N →
      (twinCount (2 ^ (N + 1)) : ℝ) / 2 ^ N ≤ c * ((Nat.log 2 N : ℝ) + 1) ^ 2 / N ^ 2 := by
  obtain ⟨C, A, hC, hCbound⟩ := exists_prod_one_add_bound
  set c₀ := ⌈C⌉₊ with hc₀
  have hCle : C ≤ 2 ^ c₀ := by
    have h1 : C ≤ (c₀ : ℝ) := Nat.le_ceil C
    have h2 : (c₀ : ℝ) ≤ 2 ^ c₀ := by exact_mod_cast (Nat.lt_two_pow_self (n := c₀)).le
    linarith
  set b := 2 * c₀ + 2 * A + 5 with hb
  obtain ⟨N₁, hN₁⟩ := exists_log_poly_bound (16 * b + 16) 1
  refine ⟨4 + 512 * (b:ℝ) ^ 2 / (Real.log 2) ^ 2, max N₁ 1, fun N hN => ?_⟩
  have hN1 : 1 ≤ N := le_trans (le_max_right _ _) hN
  set L := Nat.log 2 N + 1 with hL
  have hLpos : 1 ≤ L := by omega
  have hNL : N < 2 ^ L := Nat.lt_pow_succ_log_self (by norm_num) N
  have hlin : (16 * b + 16) * L ≤ N := by
    have := hN₁ N (le_trans (le_max_left _ _) hN)
    simpa [hL, pow_one] using this
  set k := 2 * (c₀ + (A + 2) * L) with hk
  set K := k + 1 with hK
  have hKb : K ≤ b * L := by
    have h1 : c₀ ≤ c₀ * L := Nat.le_mul_of_pos_right _ (by omega)
    have h2 : b * L = 2 * (c₀ * L) + (2 * A + 4) * L + L := by rw [hb]; ring
    have h3 : K = 2 * c₀ + (2 * A + 4) * L + 1 := by rw [hK, hk]; ring
    omega
  -- elementary facts about the sifting level `M`
  set M := N / (4 * K) with hM
  have hKpos : 0 < K := by omega
  have hd1 : (4 * K) * M + N % (4 * K) = N := Nat.div_add_mod N (4 * K)
  have hd2 : N % (4 * K) < 4 * K := Nat.mod_lt _ (by omega)
  have hd3 : (4 * K) * M = 4 * (K * M) := by ring
  have hA4 : 4 * (K * M) ≤ N := by omega
  have hBlt : N < 4 * (K * M) + 4 * K := by omega
  have hbL : (16 * b + 16) * L = 16 * (b * L) + 16 * L := by ring
  have h16K : 16 * K ≤ N := by omega
  have h16L : 16 * L ≤ N := by omega
  have hNle : N ≤ 8 * (K * M) := by omega
  have hM2 : 2 ≤ M := by
    by_contra hcon
    have hM1 : M ≤ 1 := by omega
    have : K * M ≤ K * 1 := Nat.mul_le_mul_left K hM1
    omega
  have hkM : k * (M + 1) ≤ K * M + K := by
    have e1 : k * (M + 1) = k * M + k := by ring
    have e2 : k * M ≤ K * M := Nat.mul_le_mul_right M (by omega)
    omega
  have hC1 : k * (M + 1) + 1 + 2 * L ≤ N := by omega
  have hC2 : M + 1 + 2 * L ≤ N := by
    have : M ≤ K * M := Nat.le_mul_of_pos_left M hKpos
    omega
  have hNbL : N ≤ 8 * (b * L * M) := by
    have : K * M ≤ (b * L) * M := Nat.mul_le_mul_right M hKb
    omega
  have hMN : M ≤ N := by
    have : M ≤ K * M := Nat.le_mul_of_pos_left M hKpos
    omega
  -- the sieve bound with these parameters
  set z := 2 ^ M with hz
  have hz3 : 3 ≤ z := by
    have h4 : (2:ℕ) ^ 2 ≤ 2 ^ M := Nat.pow_le_pow_right (by norm_num) hM2
    simp only [hz]; omega
  have hkeven : Even k := ⟨c₀ + (A + 2) * L, by rw [hk]; ring⟩
  have hmain := twinCount_le (2 ^ (N + 1)) z k hz3 hkeven
  have hzcast : ((z : ℕ) : ℝ) = (2:ℝ) ^ M := by rw [hz]; push_cast; ring
  have hxcast : (((2:ℕ) ^ (N + 1) : ℕ) : ℝ) = (2:ℝ) ^ (N + 1) := by push_cast; ring
  rw [hzcast, hxcast] at hmain
  have hPb : (∏ p ∈ (z + 1).primesBelow, (1 + 4 / (p : ℝ)))
      ≤ C * (Real.log ((2:ℝ) ^ M)) ^ A := by
    have := hCbound z hz3
    rwa [hzcast] at this
  have hn : (0:ℝ) < (N:ℝ) := by exact_mod_cast hN1
  have h2Npos : (0:ℝ) < (2:ℝ) ^ N := by positivity
  have hLcast : ((L : ℕ) : ℝ) = (Nat.log 2 N : ℝ) + 1 := by rw [hL]; push_cast; ring
  rw [div_le_iff₀ h2Npos, ← hLcast]
  -- the two elementary terms
  have hB1 : (2:ℝ) ^ M + 1 ≤ (2:ℝ) ^ N / (N:ℝ) ^ 2 := by
    have hnat : (2 ^ M + 1) * N ^ 2 ≤ 2 ^ N := by
      have h1 : N ^ 2 ≤ 2 ^ (2 * L) := by
        calc N ^ 2 ≤ (2 ^ L) ^ 2 := Nat.pow_le_pow_left hNL.le 2
          _ = 2 ^ (2 * L) := by rw [← pow_mul, Nat.mul_comm]
      have h2 : 2 ^ M + 1 ≤ 2 ^ (M + 1) := by
        have : 1 ≤ 2 ^ M := Nat.one_le_two_pow
        rw [pow_succ]; omega
      calc (2 ^ M + 1) * N ^ 2 ≤ 2 ^ (M + 1) * 2 ^ (2 * L) := Nat.mul_le_mul h2 h1
        _ = 2 ^ (M + 1 + 2 * L) := by rw [← pow_add]
        _ ≤ 2 ^ N := Nat.pow_le_pow_right (by norm_num) hC2
    have hcast : ((2:ℝ) ^ M + 1) * (N:ℝ) ^ 2 ≤ (2:ℝ) ^ N := by exact_mod_cast hnat
    rw [le_div_iff₀ (by positivity)]
    linarith
  have hB4 : 2 * (2 * (2:ℝ) ^ M) ^ k ≤ (2:ℝ) ^ N / (N:ℝ) ^ 2 := by
    have hnat : 2 * (2 * 2 ^ M) ^ k * N ^ 2 ≤ 2 ^ N := by
      have h1 : N ^ 2 ≤ 2 ^ (2 * L) := by
        calc N ^ 2 ≤ (2 ^ L) ^ 2 := Nat.pow_le_pow_left hNL.le 2
          _ = 2 ^ (2 * L) := by rw [← pow_mul, Nat.mul_comm]
      have h2 : 2 * (2 * 2 ^ M) ^ k = 2 ^ (k * (M + 1) + 1) := by
        rw [show (2 : ℕ) * 2 ^ M = 2 ^ (M + 1) by rw [pow_succ]; ring, ← pow_mul]
        rw [pow_succ]; ring_nf
      rw [h2]
      calc 2 ^ (k * (M + 1) + 1) * N ^ 2 ≤ 2 ^ (k * (M + 1) + 1) * 2 ^ (2 * L) :=
            Nat.mul_le_mul_left _ h1
        _ = 2 ^ (k * (M + 1) + 1 + 2 * L) := by rw [← pow_add]
        _ ≤ 2 ^ N := Nat.pow_le_pow_right (by norm_num) hC1
    have hcast : 2 * (2 * (2:ℝ) ^ M) ^ k * (N:ℝ) ^ 2 ≤ (2:ℝ) ^ N := by exact_mod_cast hnat
    rw [le_div_iff₀ (by positivity)]
    linarith
  exact twinCount_block_combine b N L M k A c₀ C _ ((2:ℝ) ^ N / (N:ℝ) ^ 2) _ hC hCle hN1
    hLpos hNL hMN hM2 hk hNbL hPb rfl hB1 hB4 hmain

/-- `∑ (log₂ N + 1)^2 / N^2` converges (comparison with `N^{-3/2}`). -/
lemma summable_log_sq_div_sq :
    Summable (fun N : ℕ => ((Nat.log 2 N : ℝ) + 1) ^ 2 / N ^ 2) := by
  obtain ⟨N₀, hN₀⟩ := exists_log_poly_bound 1 4
  set n₀ := max N₀ 1 with hn₀
  have hg : Summable (fun n : ℕ => 1 / ((n:ℝ) * Real.sqrt n)) := by
    have h : Summable (fun n : ℕ => 1 / (n:ℝ) ^ ((3:ℝ)/2)) :=
      Real.summable_one_div_nat_rpow.mpr (by norm_num)
    refine h.congr fun n => ?_
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · norm_num
    · have hn' : (0:ℝ) < n := by exact_mod_cast hn
      rw [show (3:ℝ)/2 = 1 + 1/2 by norm_num, Real.rpow_add hn', Real.rpow_one,
        ← Real.sqrt_eq_rpow]
  rw [← summable_nat_add_iff n₀]
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
    ((summable_nat_add_iff n₀).mpr hg)
  set N := n + n₀ with hN
  have hN1 : 1 ≤ N := by omega
  have hNn : N₀ ≤ N := by omega
  have hL4 : (Nat.log 2 N + 1) ^ 4 ≤ N := by simpa using hN₀ N hNn
  have hn' : (0:ℝ) < (N:ℝ) := by exact_mod_cast hN1
  set L := ((Nat.log 2 N : ℝ) + 1) with hLdef
  have hL4' : L ^ 4 ≤ (N:ℝ) := by
    have hcast : (((Nat.log 2 N + 1) ^ 4 : ℕ) : ℝ) ≤ (N:ℝ) := by exact_mod_cast hL4
    push_cast at hcast
    linarith
  have hsqrt : L ^ 2 ≤ Real.sqrt N := by
    rw [show L ^ 2 = Real.sqrt (L ^ 4) by
      rw [show L ^ 4 = (L ^ 2) ^ 2 by ring, Real.sqrt_sq (by positivity)]]
    exact Real.sqrt_le_sqrt hL4'
  have hsq : Real.sqrt N * Real.sqrt N = (N:ℝ) := Real.mul_self_sqrt hn'.le
  have hspos : 0 < Real.sqrt N := Real.sqrt_pos.mpr hn'
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  calc L ^ 2 * ((N:ℝ) * Real.sqrt N) ≤ Real.sqrt N * ((N:ℝ) * Real.sqrt N) :=
        mul_le_mul_of_nonneg_right hsqrt (by positivity)
    _ = 1 * (N:ℝ) ^ 2 := by rw [one_mul]; nlinarith [hsq]

/-- The dyadic block sums `twinCount (2^(N+1)) / 2^N` are summable. -/
theorem summable_twinCount_blocks :
    Summable (fun N : ℕ => (twinCount (2 ^ (N + 1)) : ℝ) / 2 ^ N) := by
  obtain ⟨c, N₀, hbound⟩ := exists_twinCount_block_bound
  have hg : Summable (fun N : ℕ => c * (((Nat.log 2 N : ℝ) + 1) ^ 2 / N ^ 2)) :=
    summable_log_sq_div_sq.mul_left c
  rw [← summable_nat_add_iff N₀]
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
    ((summable_nat_add_iff N₀).mpr hg)
  calc (twinCount (2 ^ (n + N₀ + 1)) : ℝ) / 2 ^ (n + N₀)
      ≤ c * ((Nat.log 2 (n + N₀) : ℝ) + 1) ^ 2 / (n + N₀ : ℕ) ^ 2 := hbound (n + N₀) (by omega)
    _ = c * (((Nat.log 2 (n + N₀) : ℝ) + 1) ^ 2 / (n + N₀ : ℕ) ^ 2) := by ring

/-- The twin primes in the dyadic block `[2^N, 2^(N+1))` contribute at most
`twinCount (2^(N+1)) / 2^N` to the sum of reciprocals. -/
lemma sum_indicator_block_le (n N : ℕ) :
    ∑ i ∈ (Finset.range n).filter (fun i => Nat.log 2 i = N),
      Set.indicator {p : ℕ | p.Prime ∧ (p + 2).Prime} (fun m => (1 : ℝ) / m) i
      ≤ (twinCount (2 ^ (N + 1)) : ℝ) / 2 ^ N := by
  classical
  set S := (Finset.range n).filter (fun i => Nat.log 2 i = N) with hS
  have hstep : ∀ i ∈ S,
      Set.indicator {p : ℕ | p.Prime ∧ (p + 2).Prime} (fun m => (1 : ℝ) / m) i
        ≤ (if (i.Prime ∧ (i + 2).Prime) then ((1:ℝ) / 2 ^ N) else 0) := by
    intro i hi
    by_cases hti : i.Prime ∧ (i + 2).Prime
    · rw [Set.indicator_of_mem (show i ∈ {p : ℕ | p.Prime ∧ (p + 2).Prime} from hti),
        if_pos hti]
      have hipos : 0 < i := hti.1.pos
      have hlog : Nat.log 2 i = N := (Finset.mem_filter.mp hi).2
      have hile : (2:ℕ) ^ N ≤ i := by
        have := Nat.pow_log_le_self 2 hipos.ne'
        rwa [hlog] at this
      have hR : ((2:ℝ) ^ N) ≤ (i:ℝ) := by exact_mod_cast hile
      exact one_div_le_one_div_of_le (by positivity) hR
    · rw [Set.indicator_of_notMem (show i ∉ {p : ℕ | p.Prime ∧ (p + 2).Prime} from hti),
        if_neg hti]
  refine (Finset.sum_le_sum hstep).trans ?_
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero, add_zero, nsmul_eq_mul]
  have hcard : #(S.filter (fun i => i.Prime ∧ (i + 2).Prime)) ≤ twinCount (2 ^ (N + 1)) := by
    rw [twinCount]
    apply Finset.card_le_card
    intro i hi
    rw [Finset.mem_filter] at hi ⊢
    obtain ⟨hiS, hti⟩ := hi
    refine ⟨Finset.mem_range.mpr ?_, hti⟩
    have hlog : Nat.log 2 i = N := (Finset.mem_filter.mp hiS).2
    have hlt := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) i
    rw [hlog] at hlt
    omega
  have hcastc : ((#(S.filter (fun i => i.Prime ∧ (i + 2).Prime)) : ℝ))
      ≤ (twinCount (2 ^ (N + 1)) : ℝ) := by exact_mod_cast hcard
  calc (#(S.filter (fun i => i.Prime ∧ (i + 2).Prime)) : ℝ) * (1 / 2 ^ N)
      ≤ (twinCount (2 ^ (N + 1)) : ℝ) * (1 / 2 ^ N) :=
        mul_le_mul_of_nonneg_right hcastc (by positivity)
    _ = (twinCount (2 ^ (N + 1)) : ℝ) / 2 ^ N := by ring

/-- The indicator function of the twin primes, weighted by `1/p`, is summable. -/
theorem summable_twin_indicator :
    Summable (Set.indicator {p : ℕ | p.Prime ∧ (p + 2).Prime} (fun n => (1 : ℝ) / n)) := by
  classical
  set f := Set.indicator {p : ℕ | p.Prime ∧ (p + 2).Prime} (fun n => (1 : ℝ) / n) with hf
  have hf0 : ∀ n, 0 ≤ f n := fun n =>
    Set.indicator_nonneg (fun a _ => by positivity) n
  refine summable_of_sum_range_le (c := ∑' N, (twinCount (2 ^ (N + 1)) : ℝ) / 2 ^ N)
    hf0 (fun n => ?_)
  have hmaps : ∀ i ∈ Finset.range n, Nat.log 2 i ∈ Finset.range n := by
    intro i hi
    rw [Finset.mem_range] at hi ⊢
    exact lt_of_le_of_lt (Nat.log_le_self 2 i) hi
  rw [← Finset.sum_fiberwise_of_maps_to hmaps f]
  calc ∑ N ∈ Finset.range n, ∑ i ∈ Finset.range n with Nat.log 2 i = N, f i
      ≤ ∑ N ∈ Finset.range n, (twinCount (2 ^ (N + 1)) : ℝ) / 2 ^ N :=
        Finset.sum_le_sum fun N _ => sum_indicator_block_le n N
    _ ≤ ∑' N, (twinCount (2 ^ (N + 1)) : ℝ) / 2 ^ N :=
        Summable.sum_le_tsum _ (fun i _ => by positivity) summable_twinCount_blocks

end Brun

import Mathlib

/-!
# Products over primes

Two estimates over the primes `p ≤ z`:

* `Brun.prod_odd_one_sub_two_div_le`: `∏_{2 < p ≤ z} (1 - 2/p) ≤ 4 / (log z)^2`, which follows
  from the elementary Euler-product bound `∏_{p ≤ z} (1 - 1/p)⁻¹ ≥ ∑_{n ≤ z} 1/n ≥ log z`.
* `Brun.exists_prod_one_add_bound`: `∏_{p ≤ z} (1 + 4/p) ≤ C (log z)^A` for suitable constants,
  a consequence of Chebyshev's bound `primorial n ≤ 4^n` (a Mertens-type estimate).
-/

open Finset

namespace Brun

/-- The completely multiplicative function `n ↦ 1/n`, as a monoid homomorphism. -/
noncomputable def invHom : ℕ →* ℝ where
  toFun n := (n : ℝ)⁻¹
  map_one' := by simp
  map_mul' := by intro m n; push_cast; rw [mul_inv]

lemma log_le_sum_inv (z : ℕ) (hz : 1 ≤ z) :
    Real.log z ≤ ∑ i ∈ Finset.Icc 1 z, (i : ℝ)⁻¹ := by
  have h1 := log_add_one_le_harmonic z
  have h2 : ((harmonic z : ℚ) : ℝ) = ∑ i ∈ Finset.Icc 1 z, (i:ℝ)⁻¹ := by
    rw [harmonic_eq_sum_Icc]
    push_cast
    ring
  have h3 : Real.log z ≤ Real.log ((z:ℝ) + 1) :=
    Real.log_le_log (by positivity) (by linarith)
  rw [h2] at h1
  push_cast at h1
  linarith

/-- Elementary Euler product bound: `log z ≤ ∏_{p ≤ z} (1 - 1/p)⁻¹`. -/
theorem log_le_prod_inv (z : ℕ) (hz : 1 ≤ z) :
    Real.log z ≤ ∏ p ∈ (z + 1).primesBelow, (1 - (p : ℝ)⁻¹)⁻¹ := by
  have hnorm : ∀ {p : ℕ}, p.Prime → ‖invHom p‖ < 1 := by
    intro p hp
    have h2 : (2:ℝ) ≤ p := by exact_mod_cast hp.two_le
    show |((p:ℝ)⁻¹)| < 1
    rw [abs_of_nonneg (by positivity), inv_lt_one_iff₀]
    right; linarith
  obtain ⟨-, hsum⟩ :=
    EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_geometric
      (f := invHom) hnorm ((z + 1).primesBelow)
  have hfilter : ((z + 1).primesBelow).filter Nat.Prime = (z + 1).primesBelow :=
    Finset.filter_true_of_mem fun p hp => Nat.prime_of_mem_primesBelow hp
  rw [hfilter] at hsum
  have hsub : ∀ n ∈ Finset.Icc 1 z, n ∈ Nat.factoredNumbers ((z + 1).primesBelow) := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    rw [Nat.mem_factoredNumbers]
    refine ⟨by omega, fun p hp => ?_⟩
    have hpp : p.Prime := Nat.prime_of_mem_primeFactorsList hp
    have hpn : p ≤ n := Nat.le_of_dvd (by omega) (Nat.dvd_of_mem_primeFactorsList hp)
    exact Nat.mem_primesBelow.mpr ⟨by omega, hpp⟩
  have key := sum_le_hasSum (Finset.subtype (· ∈ Nat.factoredNumbers ((z + 1).primesBelow))
    (Finset.Icc 1 z)) (fun i _ => by
      show (0:ℝ) ≤ invHom (i : ℕ)
      exact inv_nonneg.mpr (Nat.cast_nonneg _)) hsum
  rw [Finset.sum_subtype_eq_sum_filter, Finset.filter_true_of_mem hsub] at key
  exact (log_le_sum_inv z hz).trans key

lemma one_sub_inv_pos {p : ℕ} (hp : p.Prime) : (0:ℝ) < 1 - (p : ℝ)⁻¹ := by
  have h2 : (2:ℝ) ≤ p := by exact_mod_cast hp.two_le
  have : (p:ℝ)⁻¹ ≤ 1/2 := by
    rw [inv_le_comm₀ (by linarith) (by norm_num)]
    linarith
  linarith

/-- `∏_{p ≤ z} (1 - 1/p) ≤ 1 / log z`. -/
theorem prod_one_sub_inv_le (z : ℕ) (hz : 3 ≤ z) :
    ∏ p ∈ (z + 1).primesBelow, (1 - (p : ℝ)⁻¹) ≤ 1 / Real.log z := by
  have hlog : 0 < Real.log z := by
    apply Real.log_pos
    exact_mod_cast (by omega : 1 < z)
  have hprodpos : 0 < ∏ p ∈ (z + 1).primesBelow, (1 - (p : ℝ)⁻¹) :=
    Finset.prod_pos fun p hp => one_sub_inv_pos (Nat.prime_of_mem_primesBelow hp)
  have h1 := log_le_prod_inv z (by omega)
  rw [Finset.prod_inv_distrib] at h1
  rw [le_div_iff₀ hlog]
  calc (∏ p ∈ (z + 1).primesBelow, (1 - (p : ℝ)⁻¹)) * Real.log z
      ≤ (∏ p ∈ (z + 1).primesBelow, (1 - (p : ℝ)⁻¹))
        * (∏ p ∈ (z + 1).primesBelow, (1 - (p : ℝ)⁻¹))⁻¹ := by
        exact mul_le_mul_of_nonneg_left h1 hprodpos.le
    _ = 1 := mul_inv_cancel₀ hprodpos.ne'

/-- The main term of Brun's sieve: `∏_{2 < p ≤ z} (1 - 2/p) ≤ 4 / (log z)^2`. -/
theorem prod_odd_one_sub_two_div_le (z : ℕ) (hz : 3 ≤ z) :
    ∏ p ∈ ((z + 1).primesBelow.erase 2), (1 - 2 / (p : ℝ)) ≤ 4 / (Real.log z) ^ 2 := by
  have hmem : ∀ p ∈ (z + 1).primesBelow.erase 2, p.Prime ∧ p ≠ 2 := by
    intro p hp
    exact ⟨Nat.prime_of_mem_primesBelow (Finset.mem_of_mem_erase hp),
      Finset.ne_of_mem_erase hp⟩
  have h3 : ∀ p ∈ (z + 1).primesBelow.erase 2, (3:ℝ) ≤ p := by
    intro p hp
    obtain ⟨hpp, hp2⟩ := hmem p hp
    have := hpp.two_le
    have : 3 ≤ p := by omega
    exact_mod_cast this
  -- factorwise bound `1 - 2/p ≤ (1 - 1/p)^2`
  have hstep : ∏ p ∈ ((z + 1).primesBelow.erase 2), (1 - 2 / (p : ℝ))
      ≤ ∏ p ∈ ((z + 1).primesBelow.erase 2), (1 - (p : ℝ)⁻¹) ^ 2 := by
    refine Finset.prod_le_prod (fun p hp => ?_) (fun p hp => ?_)
    · have := h3 p hp
      have h2 : 2 / (p:ℝ) ≤ 2/3 := by
        apply div_le_div_of_nonneg_left (by norm_num) (by norm_num) this
      linarith
    · have hp3 := h3 p hp
      have hppos : (0:ℝ) < p := by linarith
      have hexp : (1 - (p : ℝ)⁻¹) ^ 2 = 1 - 2 / p + ((p : ℝ)⁻¹) ^ 2 := by
        field_simp; ring
      nlinarith [sq_nonneg ((p : ℝ)⁻¹)]
  refine hstep.trans ?_
  have h2mem : 2 ∈ (z + 1).primesBelow := Nat.mem_primesBelow.mpr ⟨by omega, Nat.prime_two⟩
  have hpos : ∀ p ∈ (z + 1).primesBelow, (0:ℝ) < 1 - (p:ℝ)⁻¹ :=
    fun p hp => one_sub_inv_pos (Nat.prime_of_mem_primesBelow hp)
  have hepos : (0:ℝ) < ∏ p ∈ ((z + 1).primesBelow.erase 2), (1 - (p:ℝ)⁻¹) :=
    Finset.prod_pos fun p hp => hpos p (Finset.mem_of_mem_erase hp)
  have hsplit : ∏ p ∈ (z + 1).primesBelow, (1 - (p:ℝ)⁻¹)
      = (1/2) * ∏ p ∈ ((z + 1).primesBelow.erase 2), (1 - (p:ℝ)⁻¹) := by
    rw [← Finset.prod_erase_mul _ _ h2mem]
    norm_num
    ring
  have hle := prod_one_sub_inv_le z hz
  rw [hsplit] at hle
  have hlog : 0 < Real.log z := Real.log_pos (by exact_mod_cast (by omega : 1 < z))
  have h2 : ∏ p ∈ ((z + 1).primesBelow.erase 2), (1 - (p:ℝ)⁻¹) ≤ 2 / Real.log z := by
    have h22 : (2:ℝ) / Real.log z = 2 * (1 / Real.log z) := by ring
    rw [h22]
    linarith
  rw [Finset.prod_pow]
  calc (∏ p ∈ ((z + 1).primesBelow.erase 2), (1 - (p:ℝ)⁻¹)) ^ 2 ≤ (2 / Real.log z) ^ 2 :=
        pow_le_pow_left₀ hepos.le h2 2
    _ = 4 / (Real.log z) ^ 2 := by rw [div_pow]; norm_num

/-- Chebyshev's bound `primorial n ≤ 4 ^ n` gives that the number of primes in the dyadic block
`[2^j, 2^(j+1))` is at most `2^(j+2)/j`. -/
lemma card_dyadic_block_mul_le (z j : ℕ) :
    (#((z + 1).primesBelow.filter (fun p => Nat.log 2 p = j))) * j ≤ 2 ^ (j + 2) := by
  set S := (z + 1).primesBelow.filter (fun p => Nat.log 2 p = j) with hS
  have hmem : ∀ p ∈ S, p.Prime ∧ 2 ^ j ≤ p ∧ p < 2 ^ (j + 1) := by
    intro p hp
    rw [hS, Finset.mem_filter] at hp
    obtain ⟨hp1, hp2⟩ := hp
    have hpp := Nat.prime_of_mem_primesBelow hp1
    refine ⟨hpp, ?_, ?_⟩
    · have := Nat.pow_log_le_self 2 hpp.pos.ne'
      rwa [hp2] at this
    · have := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) p
      rwa [hp2] at this
  have hlow : (2 ^ j) ^ (#S) ≤ ∏ p ∈ S, p :=
    Finset.pow_card_le_prod S _ _ (fun p hp => (hmem p hp).2.1)
  have hsub : S ⊆ (Finset.range (2 ^ (j + 1) + 1)).filter Nat.Prime := by
    intro p hp
    have := hmem p hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), this.1⟩
  have hhigh : ∏ p ∈ S, p ≤ primorial (2 ^ (j + 1)) := by
    rw [primorial]
    exact Finset.prod_le_prod_of_subset_of_one_le' hsub
      (fun i hi _ => (Finset.mem_filter.mp hi).2.one_lt.le)
  have h4 : primorial (2 ^ (j + 1)) ≤ 4 ^ (2 ^ (j + 1)) := primorial_le_4_pow _
  have key : (2:ℕ) ^ (j * #S) ≤ 2 ^ (2 ^ (j + 2)) := by
    calc (2:ℕ) ^ (j * #S) = (2 ^ j) ^ (#S) := by rw [pow_mul]
      _ ≤ 4 ^ (2 ^ (j + 1)) := le_trans hlow (hhigh.trans h4)
      _ = 2 ^ (2 ^ (j + 2)) := by
          rw [show (4:ℕ) = 2 ^ 2 by norm_num, ← pow_mul]
          ring_nf
  have h := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp key
  rw [Nat.mul_comm]
  exact h

/-- The reciprocals of the primes in a dyadic block `[2^j, 2^(j+1))` sum to at most `4/j`. -/
lemma sum_inv_dyadic_block_le (z j : ℕ) (hj : 1 ≤ j) :
    ∑ p ∈ (z + 1).primesBelow.filter (fun p => Nat.log 2 p = j), (1 : ℝ) / p ≤ 4 / j := by
  set S := (z + 1).primesBelow.filter (fun p => Nat.log 2 p = j) with hS
  have hlow : ∀ p ∈ S, 2 ^ j ≤ p := by
    intro p hp
    rw [hS, Finset.mem_filter] at hp
    have hpp := Nat.prime_of_mem_primesBelow hp.1
    have := Nat.pow_log_le_self 2 hpp.pos.ne'
    rwa [hp.2] at this
  have hcard := card_dyadic_block_mul_le z j
  have h1 : ∑ p ∈ S, (1 : ℝ) / p ≤ ∑ _p ∈ S, (1:ℝ) / 2 ^ j := by
    refine Finset.sum_le_sum fun p hp => ?_
    have := hlow p hp
    have h2 : (0:ℝ) < 2 ^ j := by positivity
    apply one_div_le_one_div_of_le h2
    exact_mod_cast this
  rw [Finset.sum_const, nsmul_eq_mul] at h1
  refine h1.trans ?_
  have hjR : (0:ℝ) < j := by exact_mod_cast hj
  have h2 : (0:ℝ) < 2 ^ j := by positivity
  have hc : (#S : ℝ) * j ≤ 2 ^ (j + 2) := by exact_mod_cast hcard
  have h4 : (2:ℝ) ^ (j + 2) = 4 * 2 ^ j := by ring
  rw [mul_one_div, div_le_div_iff₀ h2 hjR]
  linarith

/-- A weak Mertens estimate: `∑_{p ≤ z} 1/p ≤ 4 (1 + log (log₂ z))`. -/
theorem sum_inv_primesBelow_le (z : ℕ) :
    ∑ p ∈ (z + 1).primesBelow, (1 : ℝ) / p
      ≤ 4 * (1 + Real.log (Nat.log 2 z)) := by
  set J := Nat.log 2 z with hJ
  have hmaps : ∀ p ∈ (z + 1).primesBelow, Nat.log 2 p ∈ Finset.Icc 1 J := by
    intro p hp
    have hpp := Nat.prime_of_mem_primesBelow hp
    have hplt : p < z + 1 := Nat.lt_of_mem_primesBelow hp
    refine Finset.mem_Icc.mpr ⟨?_, ?_⟩
    · have : 1 ≤ Nat.log 2 p := by
        rw [Nat.one_le_iff_ne_zero, Ne, Nat.log_eq_zero_iff]
        push_neg
        exact ⟨hpp.two_le, by norm_num⟩
      exact this
    · exact Nat.log_mono_right (by omega)
  have hfib := Finset.sum_fiberwise_of_maps_to hmaps (fun p => (1 : ℝ) / p)
  rw [← hfib]
  have hbound : ∑ j ∈ Finset.Icc 1 J, ∑ p ∈ (z + 1).primesBelow with Nat.log 2 p = j, (1:ℝ) / p
      ≤ ∑ j ∈ Finset.Icc 1 J, (4 : ℝ) / j := by
    refine Finset.sum_le_sum fun j hj => ?_
    exact sum_inv_dyadic_block_le z j (Finset.mem_Icc.mp hj).1
  refine hbound.trans ?_
  have hharm : ∑ j ∈ Finset.Icc 1 J, (4 : ℝ) / j = 4 * ((harmonic J : ℚ) : ℝ) := by
    rw [harmonic_eq_sum_Icc]
    push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => by rw [div_eq_mul_inv]
  rw [hharm]
  have := harmonic_le_one_add_log J
  linarith

/-- A Mertens-type upper bound: `∏_{p ≤ z} (1 + 4/p)` grows at most like a power of `log z`. -/
theorem exists_prod_one_add_bound :
    ∃ (C : ℝ) (A : ℕ), 0 < C ∧ ∀ z : ℕ, 3 ≤ z →
      ∏ p ∈ (z + 1).primesBelow, (1 + 4 / (p : ℝ)) ≤ C * (Real.log z) ^ A := by
  refine ⟨Real.exp 16 / (Real.log 2) ^ 16, 16, by positivity, fun z hz => ?_⟩
  set J := Nat.log 2 z with hJ
  have hJ1 : 1 ≤ J := by
    rw [hJ, Nat.one_le_iff_ne_zero, Ne, Nat.log_eq_zero_iff]
    push_neg
    exact ⟨by omega, by norm_num⟩
  have hJR : (1:ℝ) ≤ J := by exact_mod_cast hJ1
  -- `∏ (1 + 4/p) ≤ exp (∑ 4/p)`
  have hprodexp : ∏ p ∈ (z + 1).primesBelow, (1 + 4 / (p : ℝ))
      ≤ Real.exp (∑ p ∈ (z + 1).primesBelow, 4 / (p : ℝ)) := by
    rw [Real.exp_sum]
    refine Finset.prod_le_prod (fun p hp => ?_) (fun p hp => ?_)
    · have : (0:ℝ) ≤ 4 / p := by positivity
      linarith
    · have := Real.add_one_le_exp (4 / (p:ℝ))
      linarith
  have hsum : ∑ p ∈ (z + 1).primesBelow, 4 / (p : ℝ)
      ≤ 16 * (1 + Real.log J) := by
    have h := sum_inv_primesBelow_le z
    have heq : ∑ p ∈ (z + 1).primesBelow, 4 / (p : ℝ)
        = 4 * ∑ p ∈ (z + 1).primesBelow, (1:ℝ) / p := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun p _ => by ring
    rw [heq]
    linarith
  have hexpmono := Real.exp_le_exp.mpr hsum
  have hval : Real.exp (16 * (1 + Real.log J)) = Real.exp 16 * (J : ℝ) ^ 16 := by
    have hJpos : (0:ℝ) < J := by linarith
    rw [mul_add, mul_one, Real.exp_add]
    congr 1
    rw [show (16:ℝ) = ((16:ℕ):ℝ) by norm_num, Real.exp_nat_mul, Real.exp_log hJpos]
  -- `J log 2 ≤ log z`
  have hlog2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hJlog : (J : ℝ) * Real.log 2 ≤ Real.log z := by
    have h1 : (2:ℝ) ^ J ≤ (z : ℝ) := by exact_mod_cast Nat.pow_log_le_self 2 (by omega)
    have h2 : Real.log ((2:ℝ) ^ J) ≤ Real.log z :=
      Real.log_le_log (by positivity) h1
    rwa [Real.log_pow] at h2
  have hJle : (J : ℝ) ≤ Real.log z / Real.log 2 := by
    rw [le_div_iff₀ hlog2]; exact hJlog
  calc ∏ p ∈ (z + 1).primesBelow, (1 + 4 / (p : ℝ))
      ≤ Real.exp (∑ p ∈ (z + 1).primesBelow, 4 / (p : ℝ)) := hprodexp
    _ ≤ Real.exp (16 * (1 + Real.log J)) := hexpmono
    _ = Real.exp 16 * (J : ℝ) ^ 16 := hval
    _ ≤ Real.exp 16 * (Real.log z / Real.log 2) ^ 16 := by
        gcongr
    _ = Real.exp 16 / (Real.log 2) ^ 16 * (Real.log z) ^ 16 := by
        rw [div_pow]; ring

end Brun

import Mathlib

/-!
# Bonferroni / Brun's truncated Möbius weights

We show that truncating the Möbius function to arguments with at most `k` distinct prime
factors, where `k` is even, yields an upper bound sieve in the sense of
`BoundingSieve.IsUpperMoebius`.
-/

open Finset

namespace Brun

/-- Brun's truncated Möbius weights: `μ(d)` if `d` has at most `k` distinct prime factors,
and `0` otherwise. -/
noncomputable def muPlus (k : ℕ) (d : ℕ) : ℝ :=
  if d.primeFactors.card ≤ k then (ArithmeticFunction.moebius d : ℝ) else 0

lemma abs_muPlus_le_one (k d : ℕ) : |muPlus k d| ≤ 1 := by
  unfold muPlus
  split
  · rcases eq_or_ne (ArithmeticFunction.moebius d) 0 with h | h
    · simp [h]
    · rw [ArithmeticFunction.moebius_ne_zero_iff_eq_or] at h
      rcases h with h | h <;> simp [h]
  · simp

/-- Partial alternating sums of binomial coefficients:
`∑_{j ≤ k} (-1)^j C(m+1, j) = (-1)^k C(m, k)`. -/
lemma alternating_sum_choose (m k : ℕ) :
    ∑ j ∈ range (k + 1), (-1 : ℤ) ^ j * ((m + 1).choose j) = (-1) ^ k * (m.choose k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih, Nat.choose_succ_succ' m k]
    push_cast
    ring

/-- Brun's truncated Möbius weights form an upper bound sieve when `k` is even. -/
theorem isUpperMoebius_muPlus {k : ℕ} (hk : Even k) :
    BoundingSieve.IsUpperMoebius (muPlus k) := by
  intro n
  rcases eq_or_ne n 0 with rfl | hn0
  · simp
  rcases eq_or_ne n 1 with rfl | hn1
  · simp [muPlus]
  rw [if_neg hn1]
  -- restrict to squarefree divisors
  have h1 : ∑ d ∈ n.divisors, muPlus k d = ∑ d ∈ n.divisors with Squarefree d, muPlus k d := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun d _ => ?_
    by_cases hsq : Squarefree d
    · simp [hsq]
    · simp [hsq, muPlus, ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq]
  have hfac : (UniqueFactorizationMonoid.normalizedFactors n).toFinset = n.primeFactors := by
    rw [Nat.factors_eq, ← Nat.toFinset_factors n]
    rfl
  rw [h1, Nat.sum_divisors_filter_squarefree hn0, hfac]
  let F := n.primeFactors
  have hm : F.card = n.primeFactors.card := rfl
  -- evaluate the weights on products of subsets of the prime factors
  have hval : ∀ S ∈ F.powerset, muPlus k (S.val.prod) =
      if S.card ≤ k then (-1 : ℝ) ^ S.card else 0 := by
    intro S hS
    rw [Finset.mem_powerset] at hS
    have hprime : ∀ p ∈ S, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors (hS hp)
    have hprod : S.val.prod = ∏ p ∈ S, p := by
      rw [← Finset.prod_map_val S (fun p => p), Multiset.map_id']
    have hpf : (∏ p ∈ S, p).primeFactors = S := Nat.primeFactors_prod hprime
    have hcop : (↑S : Set ℕ).Pairwise (Function.onFun Nat.Coprime id) := by
      intro a ha b hb hab
      exact (Nat.coprime_primes (hprime a ha) (hprime b hb)).mpr hab
    have hmu : ArithmeticFunction.moebius (∏ p ∈ S, p) = (-1 : ℤ) ^ S.card := by
      rw [show (∏ p ∈ S, p) = ∏ p ∈ S, id p from rfl,
        ArithmeticFunction.isMultiplicative_moebius.map_prod id S hcop]
      simp only [id_eq]
      rw [Finset.prod_congr rfl (fun p hp => ArithmeticFunction.moebius_apply_prime (hprime p hp))]
      simp
    rw [hprod, muPlus, hpf, hmu]
    split <;> simp
  rw [Finset.sum_congr rfl hval, Finset.sum_powerset]
  -- group by cardinality
  have hgroup : ∀ j ∈ range (F.card + 1),
      (∑ S ∈ Finset.powersetCard j F, if S.card ≤ k then (-1 : ℝ) ^ S.card else 0)
        = (if j ≤ k then (-1 : ℝ) ^ j * (F.card.choose j) else 0) := by
    intro j _
    rw [Finset.sum_congr rfl (fun S hS => by
      rw [(Finset.mem_powersetCard.mp hS).2])]
    rw [Finset.sum_const, Finset.card_powersetCard]
    split <;> simp [mul_comm]
  rw [Finset.sum_congr rfl hgroup]
  -- compare with the truncated alternating sum
  have hmpos : 1 ≤ F.card := by
    have : F.Nonempty := Nat.nonempty_primeFactors.mpr (by omega)
    exact Finset.card_pos.mpr this
  obtain ⟨m', hm'⟩ : ∃ m', F.card = m' + 1 := ⟨F.card - 1, by omega⟩
  rw [hm']
  have key : ∑ j ∈ range (m' + 1 + 1), (if j ≤ k then (-1 : ℝ) ^ j * ((m' + 1).choose j) else 0)
      = ∑ j ∈ range (k + 1), (-1 : ℝ) ^ j * ((m' + 1).choose j) := by
    rcases le_or_gt (m' + 1) k with hcase | hcase
    · -- the truncation is vacuous
      rw [Finset.sum_congr rfl (fun j hj => by
        rw [if_pos (by simp only [Finset.mem_range] at hj; omega)])]
      refine Finset.sum_subset (by
        intro j hj
        simp only [Finset.mem_range] at hj ⊢
        omega) ?_
      intro j hj hj'
      simp only [Finset.mem_range, not_lt] at hj hj'
      rw [Nat.choose_eq_zero_of_lt (by omega)]
      simp
    · -- the truncation cuts the sum at `k < m' + 1`
      have h2 : ∑ j ∈ range (m' + 1 + 1), (if j ≤ k then (-1 : ℝ) ^ j * ((m' + 1).choose j) else 0)
          = ∑ j ∈ range (k + 1), (if j ≤ k then (-1 : ℝ) ^ j * ((m' + 1).choose j) else 0) := by
        refine (Finset.sum_subset (by
          intro j hj
          simp only [Finset.mem_range] at hj ⊢
          omega) ?_).symm
        intro j hj hj'
        simp only [Finset.mem_range, not_lt] at hj hj'
        rw [if_neg (by omega)]
      rw [h2]
      exact Finset.sum_congr rfl fun j hj => by
        rw [if_pos (by simp only [Finset.mem_range] at hj; omega)]
  rw [key]
  have hint : ∑ j ∈ range (k + 1), (-1 : ℝ) ^ j * ((m' + 1).choose j)
      = ((∑ j ∈ range (k + 1), (-1 : ℤ) ^ j * ((m' + 1).choose j) : ℤ) : ℝ) := by
    push_cast
    ring
  rw [hint, alternating_sum_choose m' k]
  have : (0:ℤ) ≤ (-1) ^ k * (m'.choose k) := by
    rw [hk.neg_one_pow]
    positivity
  exact_mod_cast this

end Brun

import Mathlib

/-!
# Counting solutions of `d ∣ n(n+2)` in an interval

For odd squarefree `d`, the congruence `n(n+2) ≡ 0 (mod d)` has exactly `2 ^ ω(d)` solutions
modulo `d` (`Brun.card_sols`), hence the number of `n ∈ [1, x]` with `d ∣ n(n+2)` is
`x · 2^ω(d)/d` up to an error of at most `2 · 2^ω(d)` (`Brun.abs_count_sub_le`).
-/

open Finset

namespace Brun

/-- The set of residues `r < d` with `d ∣ r (r + 2)`. -/
def sols (d : ℕ) : Finset ℕ := (range d).filter (fun r => d ∣ r * (r + 2))

lemma mem_sols {d r : ℕ} : r ∈ sols d ↔ r < d ∧ d ∣ r * (r + 2) := by
  rw [sols, Finset.mem_filter, Finset.mem_range]

lemma dvd_of_modEq {d a b : ℕ} (hab : a ≡ b [MOD d]) (hb : d ∣ b * (b + 2)) :
    d ∣ a * (a + 2) := by
  have h2 : a * (a + 2) ≡ b * (b + 2) [MOD d] := Nat.ModEq.mul hab (hab.add_right 2)
  exact (Nat.modEq_zero_iff_dvd).mp (h2.trans ((Nat.modEq_zero_iff_dvd).mpr hb))

lemma dvd_mul_add_two_iff {d n : ℕ} : d ∣ n * (n + 2) ↔ d ∣ (n % d) * ((n % d) + 2) :=
  ⟨fun hh => dvd_of_modEq (Nat.mod_modEq n d) hh,
    fun hh => dvd_of_modEq (Nat.mod_modEq n d).symm hh⟩

/-! ### The number of solutions modulo `d` -/

lemma card_sols_prime {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : (sols p).card = 2 := by
  have h3 : 3 ≤ p := by
    have h2 := hp.two_le
    rcases eq_or_lt_of_le h2 with h | h
    · exact absurd h.symm hp2
    · omega
  have hset : sols p = {0, p - 2} := by
    ext r
    rw [mem_sols, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hr, hdvd⟩
      rcases (Nat.Prime.dvd_mul hp).mp hdvd with h1 | h1
      · exact Or.inl (Nat.eq_zero_of_dvd_of_lt h1 hr)
      · right
        obtain ⟨c, hc⟩ := h1
        have hc1 : c = 1 := by nlinarith
        subst hc1
        omega
    · rintro (rfl | rfl)
      · exact ⟨by omega, by simp⟩
      · refine ⟨by omega, ?_⟩
        have hpp : p - 2 + 2 = p := by omega
        rw [hpp]
        exact dvd_mul_left p (p - 2)
  rw [hset, Finset.card_insert_of_notMem (by simp; omega), Finset.card_singleton]

lemma card_sols_mul {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (h : Nat.Coprime m n) :
    (sols (m * n)).card = (sols m).card * (sols n).card := by
  rw [← Finset.card_product]
  refine Finset.card_bij' (i := fun r _ => (r % m, r % n))
    (j := fun p _ => (Nat.chineseRemainder h p.1 p.2 : ℕ)) ?_ ?_ ?_ ?_
  · intro r hr
    obtain ⟨hrlt, hrdvd⟩ := mem_sols.mp hr
    rw [Finset.mem_product]
    refine ⟨mem_sols.mpr ⟨Nat.mod_lt _ hm, ?_⟩, mem_sols.mpr ⟨Nat.mod_lt _ hn, ?_⟩⟩
    · exact dvd_of_modEq (Nat.mod_modEq r m) ((dvd_mul_right m n).trans hrdvd)
    · exact dvd_of_modEq (Nat.mod_modEq r n) ((dvd_mul_left n m).trans hrdvd)
  · intro p hp
    rw [Finset.mem_product] at hp
    obtain ⟨hp1, hd1⟩ := mem_sols.mp hp.1
    obtain ⟨hp2, hd2⟩ := mem_sols.mp hp.2
    have hcr := (Nat.chineseRemainder h p.1 p.2).2
    refine mem_sols.mpr ⟨Nat.chineseRemainder_lt_mul h p.1 p.2 hm.ne' hn.ne', ?_⟩
    exact Nat.Coprime.mul_dvd_of_dvd_of_dvd h (dvd_of_modEq hcr.1 hd1) (dvd_of_modEq hcr.2 hd2)
  · intro r hr
    obtain ⟨hrlt, hrdvd⟩ := mem_sols.mp hr
    have hcr := (Nat.chineseRemainder h (r % m) (r % n)).2
    have hkm : (Nat.chineseRemainder h (r % m) (r % n) : ℕ) ≡ r [MOD m] :=
      hcr.1.trans (Nat.mod_modEq r m)
    have hkn : (Nat.chineseRemainder h (r % m) (r % n) : ℕ) ≡ r [MOD n] :=
      hcr.2.trans (Nat.mod_modEq r n)
    have hmn := (Nat.modEq_and_modEq_iff_modEq_mul h).mp ⟨hkm, hkn⟩
    have hlt := Nat.chineseRemainder_lt_mul h (r % m) (r % n) hm.ne' hn.ne'
    rw [Nat.ModEq, Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt hrlt] at hmn
    exact hmn
  · intro p hp
    rw [Finset.mem_product] at hp
    obtain ⟨hp1, _⟩ := mem_sols.mp hp.1
    obtain ⟨hp2, _⟩ := mem_sols.mp hp.2
    have hcr := (Nat.chineseRemainder h p.1 p.2).2
    have e1 : (Nat.chineseRemainder h p.1 p.2 : ℕ) % m = p.1 := by
      have h1 := hcr.1
      rw [Nat.ModEq, Nat.mod_eq_of_lt hp1] at h1
      exact h1
    have e2 : (Nat.chineseRemainder h p.1 p.2 : ℕ) % n = p.2 := by
      have h2 := hcr.2
      rw [Nat.ModEq, Nat.mod_eq_of_lt hp2] at h2
      exact h2
    exact Prod.ext e1 e2

/-- The number of solutions of `r (r + 2) ≡ 0 (mod d)`, as an arithmetic function. -/
def solCount : ArithmeticFunction ℕ := ⟨fun d => (sols d).card, by simp [sols]⟩

lemma solCount_apply (d : ℕ) : solCount d = (sols d).card := rfl

lemma solCount_mult : solCount.IsMultiplicative := by
  constructor
  · rw [solCount_apply]
    have : sols 1 = {0} := by
      ext r
      rw [mem_sols, Finset.mem_singleton]
      constructor
      · rintro ⟨hr, -⟩; omega
      · rintro rfl; exact ⟨by omega, one_dvd _⟩
    rw [this, Finset.card_singleton]
  · intro m n hmn
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · rw [Nat.coprime_zero_left] at hmn
      subst hmn
      simp [solCount_apply, sols]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [Nat.coprime_zero_right] at hmn
      subst hmn
      simp [solCount_apply, sols]
    simp only [solCount_apply]
    exact card_sols_mul hm hn hmn

/-- For odd squarefree `d`, the congruence `r(r+2) ≡ 0 (mod d)` has `2 ^ ω(d)` solutions. -/
theorem card_sols (d : ℕ) (hodd : Odd d) (hsq : Squarefree d) :
    (sols d).card = 2 ^ d.primeFactors.card := by
  have h := solCount_mult.prod_primeFactors hsq
  rw [← solCount_apply, ← h]
  have heq : ∀ p ∈ d.primeFactors, solCount p = 2 := by
    intro p hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hp2 : p ≠ 2 := by
      rintro rfl
      have : (2:ℕ) ∣ d := Nat.dvd_of_mem_primeFactors hp
      rw [Nat.odd_iff] at hodd
      omega
    rw [solCount_apply, card_sols_prime hpp hp2]
  rw [Finset.prod_congr rfl heq, Finset.prod_const]

/-! ### Counting solutions in an interval -/

lemma count_range_eq (y : ℕ) {d : ℕ} (hd : 0 < d) :
    ((range y).filter (fun n => d ∣ n * (n + 2))).card
      = ∑ c ∈ sols d, (y / d + if c % d < y % d then 1 else 0) := by
  rw [Finset.card_eq_sum_card_fiberwise (f := fun n => n % d) (t := sols d) ?_]
  · refine Finset.sum_congr rfl fun c hc => ?_
    obtain ⟨hcd, hcs⟩ := mem_sols.mp hc
    have heq : ((range y).filter (fun n => d ∣ n * (n + 2))).filter (fun n => n % d = c)
        = (range y).filter (fun n => n ≡ c [MOD d]) := by
      ext n
      simp only [Finset.mem_filter, Finset.mem_range, Nat.ModEq]
      constructor
      · rintro ⟨⟨hn, -⟩, hmod⟩
        exact ⟨hn, by rw [hmod, Nat.mod_eq_of_lt hcd]⟩
      · rintro ⟨hn, hmod⟩
        rw [Nat.mod_eq_of_lt hcd] at hmod
        exact ⟨⟨hn, by rw [dvd_mul_add_two_iff, hmod]; exact hcs⟩, hmod⟩
    rw [heq, ← Nat.count_eq_card_filter_range]
    exact Nat.count_modEq_card _ hd c
  · intro n hn
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hn
    exact Finset.mem_coe.mpr
      (mem_sols.mpr ⟨Nat.mod_lt _ hd, by rw [← dvd_mul_add_two_iff]; exact hn.2⟩)

lemma abs_count_range_sub_le (y : ℕ) {d : ℕ} (hd : 0 < d) :
    |(((range y).filter (fun n => d ∣ n * (n + 2))).card : ℝ) - y * (sols d).card / d|
      ≤ (sols d).card := by
  rw [count_range_eq y hd]
  have hsum : (∑ c ∈ sols d, (y / d + if c % d < y % d then 1 else 0))
      = (sols d).card * (y / d) + ((sols d).filter (fun c => c % d < y % d)).card := by
    rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, Finset.sum_boole]
    simp
  rw [hsum]
  push_cast
  have hT : (((sols d).filter (fun c => c % d < y % d)).card : ℝ) ≤ (sols d).card := by
    exact_mod_cast Finset.card_filter_le _ _
  have hT0 : (0:ℝ) ≤ (((sols d).filter (fun c => c % d < y % d)).card : ℝ) := by positivity
  have hd' : (0:ℝ) < d := by exact_mod_cast hd
  have hy : (y : ℝ) = d * (y / d : ℕ) + (y % d : ℕ) := by
    exact_mod_cast (Nat.div_add_mod y d).symm
  have hr : ((y % d : ℕ) : ℝ) < d := by exact_mod_cast Nat.mod_lt _ hd
  have hr0 : (0:ℝ) ≤ ((y % d : ℕ) : ℝ) := by positivity
  have hs0 : (0:ℝ) ≤ ((sols d).card : ℝ) := by positivity
  have h1 : (d : ℝ) * (y / d : ℕ) * (sols d).card / d = (y / d : ℕ) * (sols d).card := by
    field_simp
  rw [abs_le]
  refine ⟨?_, ?_⟩
  · rw [hy, add_mul, add_div, h1]
    have h2 : ((y % d : ℕ) : ℝ) * (sols d).card / d ≤ (sols d).card := by
      rw [div_le_iff₀ hd']
      nlinarith
    nlinarith
  · rw [hy, add_mul, add_div, h1]
    have h3 : (0:ℝ) ≤ ((y % d : ℕ) : ℝ) * (sols d).card / d := by positivity
    nlinarith

lemma one_le_card_sols {d : ℕ} (hd : 0 < d) : 1 ≤ (sols d).card :=
  Finset.card_pos.mpr ⟨0, mem_sols.mpr ⟨hd, by simp⟩⟩

lemma count_Icc_add_one (x d : ℕ) :
    ((range (x + 1)).filter (fun n => d ∣ n * (n + 2))).card
      = ((Finset.Icc 1 x).filter (fun n => d ∣ n * (n + 2))).card + 1 := by
  have hins : range (x + 1) = insert 0 (Finset.Icc 1 x) := by
    ext n
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
    omega
  rw [hins, Finset.filter_insert, if_pos (by simp),
    Finset.card_insert_of_notMem (by simp)]

/-- The number of `n ∈ [1, x]` with `d ∣ n (n+2)` differs from `x · 2^ω(d) / d` by at most
`2 · 2 ^ ω(d)`. -/
theorem abs_count_sub_le (x : ℕ) {d : ℕ} (hodd : Odd d) (hsq : Squarefree d) :
    |((((Finset.Icc 1 x).filter (fun n => d ∣ n * (n + 2))).card : ℝ))
        - x * 2 ^ d.primeFactors.card / d| ≤ 2 * 2 ^ d.primeFactors.card := by
  have hd : 0 < d := Nat.pos_of_ne_zero hsq.ne_zero
  have hcs : ((sols d).card : ℝ) = 2 ^ d.primeFactors.card := by
    rw [card_sols d hodd hsq]; push_cast; ring
  have hA := abs_count_range_sub_le (x + 1) hd
  rw [count_Icc_add_one x d] at hA
  rw [abs_le] at hA ⊢
  set C := ((((Finset.Icc 1 x).filter (fun n => d ∣ n * (n + 2))).card : ℝ)) with hC
  have hd' : (0:ℝ) < d := by exact_mod_cast hd
  have hs1 : (1:ℝ) ≤ ((sols d).card : ℝ) := by exact_mod_cast one_le_card_sols hd
  have hd1 : (1:ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hsd : ((sols d).card : ℝ) / d ≤ ((sols d).card : ℝ) := by
    rw [div_le_iff₀ hd']
    nlinarith
  have hsd0 : (0:ℝ) ≤ ((sols d).card : ℝ) / d := by positivity
  have hexp : ((x + 1 : ℕ) : ℝ) * ((sols d).card : ℝ) / d
      = (x : ℝ) * ((sols d).card : ℝ) / d + ((sols d).card : ℝ) / d := by
    push_cast
    ring
  rw [hexp] at hA
  push_cast at hA
  rw [← hcs]
  constructor <;> [linarith [hA.1]; linarith [hA.2]]

end Brun

import RequestProject.Brun.Bonferroni
import RequestProject.Brun.SolutionCount
import RequestProject.Brun.PrimeProducts

/-!
# Brun's pure sieve applied to the twin prime problem

We set up the sieve problem for the sequence `n (n+2)`, `1 ≤ n ≤ x`, sifted by the odd primes
`p ≤ z`, and combine Brun's truncated Möbius weights with the two estimates of
`RequestProject.Brun.PrimeProducts` to obtain an upper bound for the number of twin primes
up to `x`.
-/

open Finset

namespace Brun

/-- The number of primes `p ≤ x` such that `p + 2` is also prime. -/
def twinCount (x : ℕ) : ℕ :=
  ((range (x + 1)).filter (fun p => p.Prime ∧ (p + 2).Prime)).card

/-- The odd primes `≤ z`. -/
def oddPrimesBelow (z : ℕ) : Finset ℕ := (z + 1).primesBelow.erase 2

/-- The product of the odd primes `≤ z`. -/
def bigP (z : ℕ) : ℕ := ∏ p ∈ oddPrimesBelow z, p

lemma mem_oddPrimesBelow {z p : ℕ} : p ∈ oddPrimesBelow z ↔ p ≠ 2 ∧ p.Prime ∧ p ≤ z := by
  simp [oddPrimesBelow, Nat.mem_primesBelow, and_comm]

lemma prime_of_mem_oddPrimesBelow {z p : ℕ} (hp : p ∈ oddPrimesBelow z) : p.Prime :=
  (mem_oddPrimesBelow.mp hp).2.1

/-- A product of distinct primes is squarefree. -/
lemma squarefree_prod_primes (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) :
    Squarefree (∏ p ∈ s, p) := by
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    have hap : a.Prime := hs a (by simp)
    have hrest : Squarefree (∏ p ∈ s, p) := ih (fun p hp => hs p (by simp [hp]))
    rw [Nat.squarefree_mul_iff]
    refine ⟨?_, hap.squarefree, hrest⟩
    have hcop : Nat.Coprime a (∏ x ∈ s, x) := by
      rw [Nat.Prime.coprime_iff_not_dvd hap]
      intro hdvd
      obtain ⟨q, hq, hqd⟩ := Prime.exists_mem_finset_dvd hap.prime hdvd
      have := hs q (by simp [hq])
      rw [Nat.prime_dvd_prime_iff_eq hap this] at hqd
      exact ha (hqd ▸ hq)
    exact hcop

lemma squarefree_bigP (z : ℕ) : Squarefree (bigP z) :=
  squarefree_prod_primes _ fun _ hp => prime_of_mem_oddPrimesBelow hp

lemma primeFactors_bigP (z : ℕ) : (bigP z).primeFactors = oddPrimesBelow z :=
  Nat.primeFactors_prod fun _ hp => prime_of_mem_oddPrimesBelow hp

/-- Every divisor of `bigP z` is odd. -/
lemma odd_of_dvd_bigP {z d : ℕ} (hd : d ∣ bigP z) : Odd d := by
  rcases Nat.even_or_odd d with he | ho
  · exfalso
    have h2 : (2:ℕ) ∣ bigP z := he.two_dvd.trans hd
    have h2mem : (2:ℕ) ∈ (bigP z).primeFactors :=
      Nat.mem_primeFactors.mpr ⟨Nat.prime_two, h2, (squarefree_bigP z).ne_zero⟩
    rw [primeFactors_bigP] at h2mem
    exact (mem_oddPrimesBelow.mp h2mem).1 rfl
  · exact ho

/-- The multiplicative function `d ↦ c^ω(d) / d`. -/
noncomputable def nuc (c : ℝ) : ArithmeticFunction ℝ :=
  ⟨fun d => if d = 0 then 0 else c ^ d.primeFactors.card / d, by simp⟩

lemma nuc_apply (c : ℝ) {d : ℕ} (hd : d ≠ 0) : nuc c d = c ^ d.primeFactors.card / d := by
  simp [nuc, hd]

lemma nuc_prime (c : ℝ) {p : ℕ} (hp : p.Prime) : nuc c p = c / p := by
  rw [nuc_apply c hp.ne_zero, hp.primeFactors]
  simp

lemma nuc_mult (c : ℝ) : (nuc c).IsMultiplicative := by
  constructor
  · simp [nuc]
  · intro m n hmn
    rcases eq_or_ne m 0 with rfl | hm
    · simp [Nat.coprime_zero_left] at hmn
      subst hmn
      simp [nuc]
    rcases eq_or_ne n 0 with rfl | hn
    · simp [Nat.coprime_zero_right] at hmn
      subst hmn
      simp [nuc]
    have hcard : (m * n).primeFactors.card = m.primeFactors.card + n.primeFactors.card := by
      rw [Nat.primeFactors_mul hm hn,
        Finset.card_union_of_disjoint (Nat.Coprime.disjoint_primeFactors hmn)]
    have hm' : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm
    have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
    simp only [nuc, ArithmeticFunction.coe_mk, mul_eq_zero, hm, hn, or_self, if_false]
    rw [hcard]
    push_cast
    rw [pow_add]
    field_simp

/-- The density function of the sieve: `ν d = 2^ω(d) / d`. -/
noncomputable def nu : ArithmeticFunction ℝ := nuc 2

lemma nu_apply {d : ℕ} (hd : d ≠ 0) : nu d = 2 ^ d.primeFactors.card / d := nuc_apply 2 hd

lemma nu_nonneg (d : ℕ) : 0 ≤ nu d := by
  rcases eq_or_ne d 0 with rfl | hd
  · simp [nu, nuc]
  · rw [nu_apply hd]; positivity

lemma nu_prime {p : ℕ} (hp : p.Prime) : nu p = 2 / p := nuc_prime 2 hp

lemma nu_mult : nu.IsMultiplicative := nuc_mult 2

/-- The map `n ↦ n (n + 2)` is injective. -/
lemma mul_add_two_injective : Function.Injective (fun n : ℕ => n * (n + 2)) := by
  intro a b hab
  simp only at hab
  nlinarith [hab, sq_nonneg (a - b), sq_nonneg (b - a)]

/-- The sieve problem: the sequence `n (n + 2)` for `1 ≤ n ≤ x`, sifted by the odd primes
`p ≤ z`. -/
noncomputable def twinSieve (x z : ℕ) : BoundingSieve where
  support := (Finset.Icc 1 x).image (fun n => n * (n + 2))
  prodPrimes := bigP z
  prodPrimes_squarefree := squarefree_bigP z
  weights := fun _ => 1
  weights_nonneg := fun _ => zero_le_one
  totalMass := x
  nu := nu
  nu_mult := nu_mult
  nu_pos_of_prime := fun p hp _ => by
    rw [nu_prime hp]
    have : (0:ℝ) < p := by exact_mod_cast hp.pos
    positivity
  nu_lt_one_of_prime := fun p hp hdvd => by
    rw [nu_prime hp]
    have hmem : p ∈ oddPrimesBelow z := by
      rw [← primeFactors_bigP z, Nat.mem_primeFactors]
      exact ⟨hp, hdvd, (squarefree_bigP z).ne_zero⟩
    have hp2 : p ≠ 2 := (mem_oddPrimesBelow.mp hmem).1
    have h3 : 3 ≤ p := by have := hp.two_le; omega
    have h3' : (3:ℝ) ≤ p := by exact_mod_cast h3
    rw [div_lt_one (by linarith)]
    linarith

/-- The sifted sum of `twinSieve` counts the `n ∈ [1, x]` with `n (n+2)` coprime to all
odd primes `≤ z`. -/
lemma siftedSum_twinSieve (x z : ℕ) :
    (twinSieve x z).siftedSum =
      (((Finset.Icc 1 x).filter (fun n => Nat.Coprime (bigP z) (n * (n + 2)))).card : ℝ) := by
  rw [BoundingSieve.siftedSum, Finset.card_filter]
  push_cast
  rw [show (twinSieve x z).support = (Finset.Icc 1 x).image (fun n => n * (n + 2)) from rfl,
    Finset.sum_image (fun a _ b _ h => mul_add_two_injective h)]
  rfl

lemma multSum_twinSieve (x z : ℕ) (d : ℕ) :
    BoundingSieve.multSum (s := twinSieve x z) d =
      ((((Finset.Icc 1 x).filter (fun n => d ∣ n * (n + 2))).card : ℝ)) := by
  rw [BoundingSieve.multSum, Finset.card_filter]
  push_cast
  rw [show (twinSieve x z).support = (Finset.Icc 1 x).image (fun n => n * (n + 2)) from rfl,
    Finset.sum_image (fun a _ b _ h => mul_add_two_injective h)]
  rfl

lemma abs_rem_le (x z : ℕ) {d : ℕ} (hd : d ∣ bigP z) :
    |BoundingSieve.rem (s := twinSieve x z) d| ≤ 2 * 2 ^ d.primeFactors.card := by
  have hdne : d ≠ 0 := by
    rintro rfl
    exact (squarefree_bigP z).ne_zero (zero_dvd_iff.mp hd)
  have hsq : Squarefree d := (squarefree_bigP z).squarefree_of_dvd hd
  have hodd : Odd d := odd_of_dvd_bigP hd
  have := abs_count_sub_le x hodd hsq
  rw [BoundingSieve.rem, multSum_twinSieve]
  have hnu : (twinSieve x z).nu d = 2 ^ d.primeFactors.card / d := nu_apply hdne
  have hmass : (twinSieve x z).totalMass = (x : ℝ) := rfl
  rw [hnu, hmass]
  calc |(((Finset.Icc 1 x).filter (fun n => d ∣ n * (n + 2))).card : ℝ)
        - 2 ^ d.primeFactors.card / d * x|
      = |(((Finset.Icc 1 x).filter (fun n => d ∣ n * (n + 2))).card : ℝ)
        - x * 2 ^ d.primeFactors.card / d| := by ring_nf
    _ ≤ 2 * 2 ^ d.primeFactors.card := this

lemma twinCount_le_sifted (x z : ℕ) :
    (twinCount x : ℝ) ≤ (z + 1) + (twinSieve x z).siftedSum := by
  rw [siftedSum_twinSieve]
  have hsub : (range (x + 1)).filter (fun p => p.Prime ∧ (p + 2).Prime) ⊆
      (range (z + 1)) ∪ ((Finset.Icc 1 x).filter
        (fun n => Nat.Coprime (bigP z) (n * (n + 2)))) := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_range] at hp
    obtain ⟨hpx, hpp, hpp2⟩ := hp
    rcases le_or_gt p z with h | h
    · exact Finset.mem_union_left _ (Finset.mem_range.mpr (by omega))
    · refine Finset.mem_union_right _ (Finset.mem_filter.mpr
        ⟨Finset.mem_Icc.mpr ⟨hpp.pos, by omega⟩, ?_⟩)
      rw [bigP]
      refine Nat.Coprime.prod_left (fun q hq => ?_)
      have hqp : q.Prime := prime_of_mem_oddPrimesBelow hq
      have hqz : q ≤ z := (mem_oddPrimesBelow.mp hq).2.2
      rw [Nat.Prime.coprime_iff_not_dvd hqp]
      intro hdvd
      rcases (Nat.Prime.dvd_mul hqp).mp hdvd with h1 | h1
      · have := (Nat.prime_dvd_prime_iff_eq hqp hpp).mp h1; omega
      · have := (Nat.prime_dvd_prime_iff_eq hqp hpp2).mp h1; omega
  have hcard := Finset.card_le_card hsub
  have h2 := Finset.card_union_le (range (z + 1))
    ((Finset.Icc 1 x).filter (fun n => Nat.Coprime (bigP z) (n * (n + 2))))
  rw [twinCount]
  have : ((range (x + 1)).filter (fun p => p.Prime ∧ (p + 2).Prime)).card ≤
      (z + 1) + ((Finset.Icc 1 x).filter (fun n => Nat.Coprime (bigP z) (n * (n + 2)))).card := by
    simpa using hcard.trans h2
  exact_mod_cast this

lemma abs_moebius_le_one (d : ℕ) : |((ArithmeticFunction.moebius d : ℤ) : ℝ)| ≤ 1 := by
  rcases eq_or_ne (ArithmeticFunction.moebius d) 0 with h | h
  · simp [h]
  · rw [ArithmeticFunction.moebius_ne_zero_iff_eq_or] at h
    rcases h with h | h <;> simp [h]

lemma mainSum_le (x z k : ℕ) (hz : 3 ≤ z) :
    (twinSieve x z).mainSum (muPlus k) ≤
      4 / (Real.log z) ^ 2 + (1 / 2 : ℝ) ^ k * ∏ p ∈ (z + 1).primesBelow, (1 + 4 / (p : ℝ)) := by
  have hsq := squarefree_bigP z
  -- termwise bound: truncation costs at most the tail `(1/2)^k * 4^ω(d)/d`
  have hterm : ∀ d ∈ (bigP z).divisors,
      muPlus k d * (twinSieve x z).nu d
        ≤ (ArithmeticFunction.moebius d : ℝ) * nu d + (1 / 2 : ℝ) ^ k * nuc 4 d := by
    intro d hd
    have hd0 : d ≠ 0 := by
      have := Nat.pos_of_mem_divisors hd; omega
    have hnu : (twinSieve x z).nu d = nu d := rfl
    have h4 : nuc 4 d = 2 ^ d.primeFactors.card * nu d := by
      rw [nuc_apply 4 hd0, nu_apply hd0, show (4:ℝ) = 2 * 2 by norm_num, mul_pow]
      ring
    have hnn := nu_nonneg d
    have hpow : (0:ℝ) ≤ (1 / 2 : ℝ) ^ k * nuc 4 d := by rw [h4]; positivity
    by_cases hk : d.primeFactors.card ≤ k
    · rw [hnu, muPlus, if_pos hk]
      linarith
    · rw [hnu, muPlus, if_neg hk, zero_mul]
      have hmu : (-1:ℝ) ≤ (ArithmeticFunction.moebius d : ℝ) :=
        neg_le_of_abs_le (abs_moebius_le_one d)
      have hbig : nu d ≤ (1 / 2 : ℝ) ^ k * nuc 4 d := by
        rw [h4]
        have h1 : (1:ℝ) ≤ (1 / 2 : ℝ) ^ k * 2 ^ d.primeFactors.card := by
          rw [div_pow, one_pow, div_mul_eq_mul_div, le_div_iff₀ (by positivity), one_mul, one_mul]
          exact pow_le_pow_right₀ (by norm_num) (by omega)
        nlinarith [hnn]
      nlinarith [hmu, hnn, hbig]
  -- the main term
  have hA : ∏ p ∈ (bigP z).primeFactors, (1 - nu p) ≤ 4 / (Real.log z) ^ 2 := by
    rw [primeFactors_bigP]
    have heq : ∀ p ∈ oddPrimesBelow z, (1 - nu p) = 1 - 2 / (p:ℝ) := fun p hp => by
      rw [nu_prime (prime_of_mem_oddPrimesBelow hp)]
    rw [Finset.prod_congr rfl heq]
    exact prod_odd_one_sub_two_div_le z hz
  -- the tail term
  have hB : ∏ p ∈ (bigP z).primeFactors, (1 + nuc 4 p)
      ≤ ∏ p ∈ (z + 1).primesBelow, (1 + 4 / (p : ℝ)) := by
    rw [primeFactors_bigP]
    have heq : ∀ p ∈ oddPrimesBelow z, (1 + nuc 4 p) = 1 + 4 / (p:ℝ) := fun p hp => by
      rw [nuc_prime 4 (prime_of_mem_oddPrimesBelow hp)]
    rw [Finset.prod_congr rfl heq]
    have h2 : (2:ℕ) ∈ (z + 1).primesBelow :=
      Nat.mem_primesBelow.mpr ⟨by omega, Nat.prime_two⟩
    have hprod := Finset.prod_erase_mul (z + 1).primesBelow (fun p => 1 + 4 / (p:ℝ)) h2
    have hnn : 0 ≤ ∏ p ∈ (z + 1).primesBelow.erase 2, (1 + 4 / (p:ℝ)) := by
      refine Finset.prod_nonneg fun p _ => ?_
      have : (0:ℝ) ≤ p := Nat.cast_nonneg p
      positivity
    rw [oddPrimesBelow, ← hprod]
    norm_num
    nlinarith [hnn]
  calc (twinSieve x z).mainSum (muPlus k)
      = ∑ d ∈ (bigP z).divisors, muPlus k d * (twinSieve x z).nu d := rfl
    _ ≤ ∑ d ∈ (bigP z).divisors,
          ((ArithmeticFunction.moebius d : ℝ) * nu d + (1 / 2 : ℝ) ^ k * nuc 4 d) :=
        Finset.sum_le_sum hterm
    _ = (∑ d ∈ (bigP z).divisors, (ArithmeticFunction.moebius d : ℝ) * nu d)
          + (1 / 2 : ℝ) ^ k * ∑ d ∈ (bigP z).divisors, nuc 4 d := by
        rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ = (∏ p ∈ (bigP z).primeFactors, (1 - nu p))
          + (1 / 2 : ℝ) ^ k * ∏ p ∈ (bigP z).primeFactors, (1 + nuc 4 p) := by
        rw [ArithmeticFunction.IsMultiplicative.prodPrimeFactors_one_sub_of_squarefree nu nu_mult
          hsq, (nuc_mult 4).prodPrimeFactors_one_add_of_squarefree hsq]
    _ ≤ 4 / (Real.log z) ^ 2 + (1 / 2 : ℝ) ^ k * ∏ p ∈ (z + 1).primesBelow, (1 + 4 / (p : ℝ)) := by
        gcongr

lemma errSum_le (x z k : ℕ) (hz : 1 ≤ z) :
    (twinSieve x z).errSum (muPlus k) ≤ 2 * (2 * z : ℝ) ^ k := by
  have hterm : ∀ d ∈ (bigP z).divisors,
      |muPlus k d| * |BoundingSieve.rem (s := twinSieve x z) d|
        ≤ (if d.primeFactors.card ≤ k then 2 * (2:ℝ) ^ k else 0) := by
    intro d hd
    have hdvd : d ∣ bigP z := (Nat.mem_divisors.mp hd).1
    by_cases hk : d.primeFactors.card ≤ k
    · rw [if_pos hk]
      have h1 := abs_muPlus_le_one k d
      have h2 := abs_rem_le x z hdvd
      have h3 : (2:ℝ) ^ d.primeFactors.card ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) hk
      calc |muPlus k d| * |BoundingSieve.rem (s := twinSieve x z) d|
          ≤ 1 * (2 * 2 ^ d.primeFactors.card) := mul_le_mul h1 h2 (abs_nonneg _) zero_le_one
        _ ≤ 2 * 2 ^ k := by rw [one_mul]; linarith
    · rw [if_neg hk]
      simp [muPlus, hk]
  have hdle : ∀ d ∈ (bigP z).divisors, d.primeFactors.card ≤ k → d ≤ z ^ k := by
    intro d hd hkd
    have hdvd := (Nat.mem_divisors.mp hd).1
    have hsq : Squarefree d := (squarefree_bigP z).squarefree_of_dvd hdvd
    have hpf : d.primeFactors ⊆ oddPrimesBelow z := by
      rw [← primeFactors_bigP z]
      exact Nat.primeFactors_mono hdvd (squarefree_bigP z).ne_zero
    calc d = ∏ p ∈ d.primeFactors, p := (Nat.prod_primeFactors_of_squarefree hsq).symm
      _ ≤ ∏ _p ∈ d.primeFactors, z :=
          Finset.prod_le_prod' (fun p hp => (mem_oddPrimesBelow.mp (hpf hp)).2.2)
      _ = z ^ d.primeFactors.card := by rw [Finset.prod_const]
      _ ≤ z ^ k := Nat.pow_le_pow_right hz hkd
  have hcard : (((bigP z).divisors.filter (fun d => d.primeFactors.card ≤ k)).card : ℝ)
      ≤ (z:ℝ) ^ k := by
    have hsub : (bigP z).divisors.filter (fun d => d.primeFactors.card ≤ k)
        ⊆ Finset.Icc 1 (z ^ k) := by
      intro d hd
      rw [Finset.mem_filter] at hd
      exact Finset.mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hd.1, hdle d hd.1 hd.2⟩
    have hle := Finset.card_le_card hsub
    rw [Nat.card_Icc] at hle
    simp at hle
    exact_mod_cast hle
  rw [BoundingSieve.errSum]
  calc ∑ d ∈ (bigP z).divisors,
        |muPlus k d| * |BoundingSieve.rem (s := twinSieve x z) d|
      ≤ ∑ d ∈ (bigP z).divisors, (if d.primeFactors.card ≤ k then 2 * (2:ℝ) ^ k else 0) :=
        Finset.sum_le_sum hterm
    _ = 2 * (2:ℝ) ^ k * (((bigP z).divisors.filter (fun d => d.primeFactors.card ≤ k)).card : ℝ) := by
        rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero, add_zero, nsmul_eq_mul]
        ring
    _ ≤ 2 * (2:ℝ) ^ k * (z:ℝ) ^ k := mul_le_mul_of_nonneg_left hcard (by positivity)
    _ = 2 * (2 * z : ℝ) ^ k := by rw [mul_pow]; ring

/-- Brun's sieve bound for the number of twin primes up to `x`. -/
theorem twinCount_le (x z k : ℕ) (hz : 3 ≤ z) (hk : Even k) :
    (twinCount x : ℝ) ≤ (z + 1)
      + x * (4 / (Real.log z) ^ 2
          + (1 / 2 : ℝ) ^ k * ∏ p ∈ (z + 1).primesBelow, (1 + 4 / (p : ℝ)))
      + 2 * (2 * z : ℝ) ^ k := by
  have h1 := twinCount_le_sifted x z
  have h2 := BoundingSieve.siftedSum_le_mainSum_errSum_of_upperMoebius (s := twinSieve x z)
    (muPlus k) (isUpperMoebius_muPlus hk)
  have h3 := mainSum_le x z k hz
  have h4 := errSum_le x z k (by omega)
  have hx : (twinSieve x z).totalMass = (x : ℝ) := rfl
  rw [hx] at h2
  have hxpos : (0:ℝ) ≤ x := Nat.cast_nonneg x
  nlinarith [h1, h2, h3, h4]

end Brun

