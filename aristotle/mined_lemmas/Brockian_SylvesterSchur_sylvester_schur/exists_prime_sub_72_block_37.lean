import Mathlib
import SylvesterSchurCore
namespace Brockian.SylvesterSchur
/-- Sylvester–Schur: for n > k ≥ 1, some element of {n+1,…,n+k} has a prime factor > k. -/

lemma exists_prime_sub_72_block_37 (n : ℕ) (hlo : 92501 ≤ n) (hhi : n ≤ 95000) :
    ∃ p : ℕ, p.Prime ∧ n - 72 < p ∧ p ≤ n := by
  by_cases h0 : n ≤ 92560
  · exact ⟨92489, by norm_num, by omega, by omega⟩
  by_cases h1 : n ≤ 92628
  · exact ⟨92557, by norm_num, by omega, by omega⟩
  by_cases h2 : n ≤ 92698
  · exact ⟨92627, by norm_num, by omega, by omega⟩
  by_cases h3 : n ≤ 92770
  · exact ⟨92699, by norm_num, by omega, by omega⟩
  by_cases h4 : n ≤ 92838
  · exact ⟨92767, by norm_num, by omega, by omega⟩
  by_cases h5 : n ≤ 92902
  · exact ⟨92831, by norm_num, by omega, by omega⟩
  by_cases h6 : n ≤ 92970
  · exact ⟨92899, by norm_num, by omega, by omega⟩
  by_cases h7 : n ≤ 93030
  · exact ⟨92959, by norm_num, by omega, by omega⟩
  by_cases h8 : n ≤ 93072
  · exact ⟨93001, by norm_num, by omega, by omega⟩
  by_cases h9 : n ≤ 93130
  · exact ⟨93059, by norm_num, by omega, by omega⟩
  by_cases h10 : n ≤ 93202
  · exact ⟨93131, by norm_num, by omega, by omega⟩
  by_cases h11 : n ≤ 93270
  · exact ⟨93199, by norm_num, by omega, by omega⟩
  by_cases h12 : n ≤ 93334
  · exact ⟨93263, by norm_num, by omega, by omega⟩
  by_cases h13 : n ≤ 93400
  · exact ⟨93329, by norm_num, by omega, by omega⟩
  by_cases h14 : n ≤ 93454
  · exact ⟨93383, by norm_num, by omega, by omega⟩
  by_cases h15 : n ≤ 93498
  · exact ⟨93427, by norm_num, by omega, by omega⟩
  by_cases h16 : n ≤ 93568
  · exact ⟨93497, by norm_num, by omega, by omega⟩
  by_cases h17 : n ≤ 93634
  · exact ⟨93563, by norm_num, by omega, by omega⟩
  by_cases h18 : n ≤ 93700
  · exact ⟨93629, by norm_num, by omega, by omega⟩
  by_cases h19 : n ≤ 93772
  · exact ⟨93701, by norm_num, by omega, by omega⟩
  by_cases h20 : n ≤ 93834
  · exact ⟨93763, by norm_num, by omega, by omega⟩
  by_cases h21 : n ≤ 93898
  · exact ⟨93827, by norm_num, by omega, by omega⟩
  by_cases h22 : n ≤ 93964
  · exact ⟨93893, by norm_num, by omega, by omega⟩
  by_cases h23 : n ≤ 94020
  · exact ⟨93949, by norm_num, by omega, by omega⟩
  by_cases h24 : n ≤ 94080
  · exact ⟨94009, by norm_num, by omega, by omega⟩
  by_cases h25 : n ≤ 94150
  · exact ⟨94079, by norm_num, by omega, by omega⟩
  by_cases h26 : n ≤ 94222
  · exact ⟨94151, by norm_num, by omega, by omega⟩
  by_cases h27 : n ≤ 94290
  · exact ⟨94219, by norm_num, by omega, by omega⟩
  by_cases h28 : n ≤ 94362
  · exact ⟨94291, by norm_num, by omega, by omega⟩
  by_cases h29 : n ≤ 94422
  · exact ⟨94351, by norm_num, by omega, by omega⟩
  by_cases h30 : n ≤ 94492
  · exact ⟨94421, by norm_num, by omega, by omega⟩
  by_cases h31 : n ≤ 94554
  · exact ⟨94483, by norm_num, by omega, by omega⟩
  by_cases h32 : n ≤ 94618
  · exact ⟨94547, by norm_num, by omega, by omega⟩
  by_cases h33 : n ≤ 94684
  · exact ⟨94613, by norm_num, by omega, by omega⟩
  by_cases h34 : n ≤ 94722
  · exact ⟨94651, by norm_num, by omega, by omega⟩
  by_cases h35 : n ≤ 94794
  · exact ⟨94723, by norm_num, by omega, by omega⟩
  by_cases h36 : n ≤ 94864
  · exact ⟨94793, by norm_num, by omega, by omega⟩
  by_cases h37 : n ≤ 94920
  · exact ⟨94849, by norm_num, by omega, by omega⟩
  by_cases h38 : n ≤ 94978
  · exact ⟨94907, by norm_num, by omega, by omega⟩
  · exact ⟨94961, by norm_num, by omega, by omega⟩

set_option maxHeartbeats 800000 in
