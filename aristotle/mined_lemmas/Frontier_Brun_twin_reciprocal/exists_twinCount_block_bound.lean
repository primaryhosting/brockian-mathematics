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
