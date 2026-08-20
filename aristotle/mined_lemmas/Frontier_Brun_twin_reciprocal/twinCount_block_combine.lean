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
