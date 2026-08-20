import Mathlib
import SylvesterSchurCore
namespace Brockian.SylvesterSchur
/-- Sylvester–Schur: for n > k ≥ 1, some element of {n+1,…,n+k} has a prime factor > k. -/

lemma exists_prime_sub_72_block_7 (n : ℕ) (hlo : 17501 ≤ n) (hhi : n ≤ 20000) :
    ∃ p : ℕ, p.Prime ∧ n - 72 < p ∧ p ≤ n := by
  by_cases h0 : n ≤ 17568
  · exact ⟨17497, by norm_num, by omega, by omega⟩
  by_cases h1 : n ≤ 17640
  · exact ⟨17569, by norm_num, by omega, by omega⟩
  by_cases h2 : n ≤ 17698
  · exact ⟨17627, by norm_num, by omega, by omega⟩
  by_cases h3 : n ≤ 17754
  · exact ⟨17683, by norm_num, by omega, by omega⟩
  by_cases h4 : n ≤ 17820
  · exact ⟨17749, by norm_num, by omega, by omega⟩
  by_cases h5 : n ≤ 17878
  · exact ⟨17807, by norm_num, by omega, by omega⟩
  by_cases h6 : n ≤ 17934
  · exact ⟨17863, by norm_num, by omega, by omega⟩
  by_cases h7 : n ≤ 18000
  · exact ⟨17929, by norm_num, by omega, by omega⟩
  by_cases h8 : n ≤ 18060
  · exact ⟨17989, by norm_num, by omega, by omega⟩
  by_cases h9 : n ≤ 18132
  · exact ⟨18061, by norm_num, by omega, by omega⟩
  by_cases h10 : n ≤ 18204
  · exact ⟨18133, by norm_num, by omega, by omega⟩
  by_cases h11 : n ≤ 18270
  · exact ⟨18199, by norm_num, by omega, by omega⟩
  by_cases h12 : n ≤ 18340
  · exact ⟨18269, by norm_num, by omega, by omega⟩
  by_cases h13 : n ≤ 18412
  · exact ⟨18341, by norm_num, by omega, by omega⟩
  by_cases h14 : n ≤ 18484
  · exact ⟨18413, by norm_num, by omega, by omega⟩
  by_cases h15 : n ≤ 18552
  · exact ⟨18481, by norm_num, by omega, by omega⟩
  by_cases h16 : n ≤ 18624
  · exact ⟨18553, by norm_num, by omega, by omega⟩
  by_cases h17 : n ≤ 18688
  · exact ⟨18617, by norm_num, by omega, by omega⟩
  by_cases h18 : n ≤ 18750
  · exact ⟨18679, by norm_num, by omega, by omega⟩
  by_cases h19 : n ≤ 18820
  · exact ⟨18749, by norm_num, by omega, by omega⟩
  by_cases h20 : n ≤ 18874
  · exact ⟨18803, by norm_num, by omega, by omega⟩
  by_cases h21 : n ≤ 18940
  · exact ⟨18869, by norm_num, by omega, by omega⟩
  by_cases h22 : n ≤ 18990
  · exact ⟨18919, by norm_num, by omega, by omega⟩
  by_cases h23 : n ≤ 19050
  · exact ⟨18979, by norm_num, by omega, by omega⟩
  by_cases h24 : n ≤ 19122
  · exact ⟨19051, by norm_num, by omega, by omega⟩
  by_cases h25 : n ≤ 19192
  · exact ⟨19121, by norm_num, by omega, by omega⟩
  by_cases h26 : n ≤ 19254
  · exact ⟨19183, by norm_num, by omega, by omega⟩
  by_cases h27 : n ≤ 19320
  · exact ⟨19249, by norm_num, by omega, by omega⟩
  by_cases h28 : n ≤ 19390
  · exact ⟨19319, by norm_num, by omega, by omega⟩
  by_cases h29 : n ≤ 19462
  · exact ⟨19391, by norm_num, by omega, by omega⟩
  by_cases h30 : n ≤ 19534
  · exact ⟨19463, by norm_num, by omega, by omega⟩
  by_cases h31 : n ≤ 19602
  · exact ⟨19531, by norm_num, by omega, by omega⟩
  by_cases h32 : n ≤ 19674
  · exact ⟨19603, by norm_num, by omega, by omega⟩
  by_cases h33 : n ≤ 19732
  · exact ⟨19661, by norm_num, by omega, by omega⟩
  by_cases h34 : n ≤ 19798
  · exact ⟨19727, by norm_num, by omega, by omega⟩
  by_cases h35 : n ≤ 19864
  · exact ⟨19793, by norm_num, by omega, by omega⟩
  by_cases h36 : n ≤ 19932
  · exact ⟨19861, by norm_num, by omega, by omega⟩
  by_cases h37 : n ≤ 19998
  · exact ⟨19927, by norm_num, by omega, by omega⟩
  · exact ⟨19997, by norm_num, by omega, by omega⟩

set_option maxHeartbeats 800000 in
