import Mathlib
import SylvesterSchurCore
namespace Brockian.SylvesterSchur
/-- Sylvester–Schur: for n > k ≥ 1, some element of {n+1,…,n+k} has a prime factor > k. -/

lemma exists_prime_sub_72_block_2 (n : ℕ) (hlo : 5001 ≤ n) (hhi : n ≤ 7500) :
    ∃ p : ℕ, p.Prime ∧ n - 72 < p ∧ p ≤ n := by
  by_cases h0 : n ≤ 5070
  · exact ⟨4999, by norm_num, by omega, by omega⟩
  by_cases h1 : n ≤ 5130
  · exact ⟨5059, by norm_num, by omega, by omega⟩
  by_cases h2 : n ≤ 5190
  · exact ⟨5119, by norm_num, by omega, by omega⟩
  by_cases h3 : n ≤ 5260
  · exact ⟨5189, by norm_num, by omega, by omega⟩
  by_cases h4 : n ≤ 5332
  · exact ⟨5261, by norm_num, by omega, by omega⟩
  by_cases h5 : n ≤ 5404
  · exact ⟨5333, by norm_num, by omega, by omega⟩
  by_cases h6 : n ≤ 5470
  · exact ⟨5399, by norm_num, by omega, by omega⟩
  by_cases h7 : n ≤ 5542
  · exact ⟨5471, by norm_num, by omega, by omega⟩
  by_cases h8 : n ≤ 5602
  · exact ⟨5531, by norm_num, by omega, by omega⟩
  by_cases h9 : n ≤ 5662
  · exact ⟨5591, by norm_num, by omega, by omega⟩
  by_cases h10 : n ≤ 5730
  · exact ⟨5659, by norm_num, by omega, by omega⟩
  by_cases h11 : n ≤ 5788
  · exact ⟨5717, by norm_num, by omega, by omega⟩
  by_cases h12 : n ≤ 5854
  · exact ⟨5783, by norm_num, by omega, by omega⟩
  by_cases h13 : n ≤ 5922
  · exact ⟨5851, by norm_num, by omega, by omega⟩
  by_cases h14 : n ≤ 5994
  · exact ⟨5923, by norm_num, by omega, by omega⟩
  by_cases h15 : n ≤ 6058
  · exact ⟨5987, by norm_num, by omega, by omega⟩
  by_cases h16 : n ≤ 6124
  · exact ⟨6053, by norm_num, by omega, by omega⟩
  by_cases h17 : n ≤ 6192
  · exact ⟨6121, by norm_num, by omega, by omega⟩
  by_cases h18 : n ≤ 6244
  · exact ⟨6173, by norm_num, by omega, by omega⟩
  by_cases h19 : n ≤ 6300
  · exact ⟨6229, by norm_num, by omega, by omega⟩
  by_cases h20 : n ≤ 6372
  · exact ⟨6301, by norm_num, by omega, by omega⟩
  by_cases h21 : n ≤ 6444
  · exact ⟨6373, by norm_num, by omega, by omega⟩
  by_cases h22 : n ≤ 6498
  · exact ⟨6427, by norm_num, by omega, by omega⟩
  by_cases h23 : n ≤ 6562
  · exact ⟨6491, by norm_num, by omega, by omega⟩
  by_cases h24 : n ≤ 6634
  · exact ⟨6563, by norm_num, by omega, by omega⟩
  by_cases h25 : n ≤ 6690
  · exact ⟨6619, by norm_num, by omega, by omega⟩
  by_cases h26 : n ≤ 6762
  · exact ⟨6691, by norm_num, by omega, by omega⟩
  by_cases h27 : n ≤ 6834
  · exact ⟨6763, by norm_num, by omega, by omega⟩
  by_cases h28 : n ≤ 6904
  · exact ⟨6833, by norm_num, by omega, by omega⟩
  by_cases h29 : n ≤ 6970
  · exact ⟨6899, by norm_num, by omega, by omega⟩
  by_cases h30 : n ≤ 7042
  · exact ⟨6971, by norm_num, by omega, by omega⟩
  by_cases h31 : n ≤ 7114
  · exact ⟨7043, by norm_num, by omega, by omega⟩
  by_cases h32 : n ≤ 7180
  · exact ⟨7109, by norm_num, by omega, by omega⟩
  by_cases h33 : n ≤ 7248
  · exact ⟨7177, by norm_num, by omega, by omega⟩
  by_cases h34 : n ≤ 7318
  · exact ⟨7247, by norm_num, by omega, by omega⟩
  by_cases h35 : n ≤ 7380
  · exact ⟨7309, by norm_num, by omega, by omega⟩
  by_cases h36 : n ≤ 7440
  · exact ⟨7369, by norm_num, by omega, by omega⟩
  · exact ⟨7433, by norm_num, by omega, by omega⟩

set_option maxHeartbeats 800000 in
