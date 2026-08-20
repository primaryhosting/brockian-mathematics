import Mathlib
import SylvesterSchurCore
namespace Brockian.SylvesterSchur
/-- Sylvester–Schur: for n > k ≥ 1, some element of {n+1,…,n+k} has a prime factor > k. -/

lemma exists_prime_sub_72_block_0 (n : ℕ) (hlo : 144 ≤ n) (hhi : n ≤ 2500) :
    ∃ p : ℕ, p.Prime ∧ n - 72 < p ∧ p ≤ n := by
  by_cases h0 : n ≤ 210
  · exact ⟨139, by norm_num, by omega, by omega⟩
  by_cases h1 : n ≤ 282
  · exact ⟨211, by norm_num, by omega, by omega⟩
  by_cases h2 : n ≤ 354
  · exact ⟨283, by norm_num, by omega, by omega⟩
  by_cases h3 : n ≤ 424
  · exact ⟨353, by norm_num, by omega, by omega⟩
  by_cases h4 : n ≤ 492
  · exact ⟨421, by norm_num, by omega, by omega⟩
  by_cases h5 : n ≤ 562
  · exact ⟨491, by norm_num, by omega, by omega⟩
  by_cases h6 : n ≤ 634
  · exact ⟨563, by norm_num, by omega, by omega⟩
  by_cases h7 : n ≤ 702
  · exact ⟨631, by norm_num, by omega, by omega⟩
  by_cases h8 : n ≤ 772
  · exact ⟨701, by norm_num, by omega, by omega⟩
  by_cases h9 : n ≤ 844
  · exact ⟨773, by norm_num, by omega, by omega⟩
  by_cases h10 : n ≤ 910
  · exact ⟨839, by norm_num, by omega, by omega⟩
  by_cases h11 : n ≤ 982
  · exact ⟨911, by norm_num, by omega, by omega⟩
  by_cases h12 : n ≤ 1054
  · exact ⟨983, by norm_num, by omega, by omega⟩
  by_cases h13 : n ≤ 1122
  · exact ⟨1051, by norm_num, by omega, by omega⟩
  by_cases h14 : n ≤ 1194
  · exact ⟨1123, by norm_num, by omega, by omega⟩
  by_cases h15 : n ≤ 1264
  · exact ⟨1193, by norm_num, by omega, by omega⟩
  by_cases h16 : n ≤ 1330
  · exact ⟨1259, by norm_num, by omega, by omega⟩
  by_cases h17 : n ≤ 1398
  · exact ⟨1327, by norm_num, by omega, by omega⟩
  by_cases h18 : n ≤ 1470
  · exact ⟨1399, by norm_num, by omega, by omega⟩
  by_cases h19 : n ≤ 1542
  · exact ⟨1471, by norm_num, by omega, by omega⟩
  by_cases h20 : n ≤ 1614
  · exact ⟨1543, by norm_num, by omega, by omega⟩
  by_cases h21 : n ≤ 1684
  · exact ⟨1613, by norm_num, by omega, by omega⟩
  by_cases h22 : n ≤ 1740
  · exact ⟨1669, by norm_num, by omega, by omega⟩
  by_cases h23 : n ≤ 1812
  · exact ⟨1741, by norm_num, by omega, by omega⟩
  by_cases h24 : n ≤ 1882
  · exact ⟨1811, by norm_num, by omega, by omega⟩
  by_cases h25 : n ≤ 1950
  · exact ⟨1879, by norm_num, by omega, by omega⟩
  by_cases h26 : n ≤ 2022
  · exact ⟨1951, by norm_num, by omega, by omega⟩
  by_cases h27 : n ≤ 2088
  · exact ⟨2017, by norm_num, by omega, by omega⟩
  by_cases h28 : n ≤ 2160
  · exact ⟨2089, by norm_num, by omega, by omega⟩
  by_cases h29 : n ≤ 2232
  · exact ⟨2161, by norm_num, by omega, by omega⟩
  by_cases h30 : n ≤ 2292
  · exact ⟨2221, by norm_num, by omega, by omega⟩
  by_cases h31 : n ≤ 2364
  · exact ⟨2293, by norm_num, by omega, by omega⟩
  by_cases h32 : n ≤ 2428
  · exact ⟨2357, by norm_num, by omega, by omega⟩
  by_cases h33 : n ≤ 2494
  · exact ⟨2423, by norm_num, by omega, by omega⟩
  · exact ⟨2477, by norm_num, by omega, by omega⟩

set_option maxHeartbeats 800000 in
