import Mathlib
import SylvesterSchurCore
namespace Brockian.SylvesterSchur
/-- Sylvester–Schur: for n > k ≥ 1, some element of {n+1,…,n+k} has a prime factor > k. -/

lemma exists_prime_sub_72_block_10 (n : ℕ) (hlo : 25001 ≤ n) (hhi : n ≤ 27500) :
    ∃ p : ℕ, p.Prime ∧ n - 72 < p ∧ p ≤ n := by
  by_cases h0 : n ≤ 25060
  · exact ⟨24989, by norm_num, by omega, by omega⟩
  by_cases h1 : n ≤ 25128
  · exact ⟨25057, by norm_num, by omega, by omega⟩
  by_cases h2 : n ≤ 25198
  · exact ⟨25127, by norm_num, by omega, by omega⟩
  by_cases h3 : n ≤ 25260
  · exact ⟨25189, by norm_num, by omega, by omega⟩
  by_cases h4 : n ≤ 25332
  · exact ⟨25261, by norm_num, by omega, by omega⟩
  by_cases h5 : n ≤ 25392
  · exact ⟨25321, by norm_num, by omega, by omega⟩
  by_cases h6 : n ≤ 25462
  · exact ⟨25391, by norm_num, by omega, by omega⟩
  by_cases h7 : n ≤ 25534
  · exact ⟨25463, by norm_num, by omega, by omega⟩
  by_cases h8 : n ≤ 25594
  · exact ⟨25523, by norm_num, by omega, by omega⟩
  by_cases h9 : n ≤ 25660
  · exact ⟨25589, by norm_num, by omega, by omega⟩
  by_cases h10 : n ≤ 25728
  · exact ⟨25657, by norm_num, by omega, by omega⟩
  by_cases h11 : n ≤ 25788
  · exact ⟨25717, by norm_num, by omega, by omega⟩
  by_cases h12 : n ≤ 25842
  · exact ⟨25771, by norm_num, by omega, by omega⟩
  by_cases h13 : n ≤ 25912
  · exact ⟨25841, by norm_num, by omega, by omega⟩
  by_cases h14 : n ≤ 25984
  · exact ⟨25913, by norm_num, by omega, by omega⟩
  by_cases h15 : n ≤ 26052
  · exact ⟨25981, by norm_num, by omega, by omega⟩
  by_cases h16 : n ≤ 26124
  · exact ⟨26053, by norm_num, by omega, by omega⟩
  by_cases h17 : n ≤ 26190
  · exact ⟨26119, by norm_num, by omega, by omega⟩
  by_cases h18 : n ≤ 26260
  · exact ⟨26189, by norm_num, by omega, by omega⟩
  by_cases h19 : n ≤ 26332
  · exact ⟨26261, by norm_num, by omega, by omega⟩
  by_cases h20 : n ≤ 26392
  · exact ⟨26321, by norm_num, by omega, by omega⟩
  by_cases h21 : n ≤ 26464
  · exact ⟨26393, by norm_num, by omega, by omega⟩
  by_cases h22 : n ≤ 26530
  · exact ⟨26459, by norm_num, by omega, by omega⟩
  by_cases h23 : n ≤ 26584
  · exact ⟨26513, by norm_num, by omega, by omega⟩
  by_cases h24 : n ≤ 26644
  · exact ⟨26573, by norm_num, by omega, by omega⟩
  by_cases h25 : n ≤ 26712
  · exact ⟨26641, by norm_num, by omega, by omega⟩
  by_cases h26 : n ≤ 26784
  · exact ⟨26713, by norm_num, by omega, by omega⟩
  by_cases h27 : n ≤ 26854
  · exact ⟨26783, by norm_num, by omega, by omega⟩
  by_cases h28 : n ≤ 26920
  · exact ⟨26849, by norm_num, by omega, by omega⟩
  by_cases h29 : n ≤ 26992
  · exact ⟨26921, by norm_num, by omega, by omega⟩
  by_cases h30 : n ≤ 27064
  · exact ⟨26993, by norm_num, by omega, by omega⟩
  by_cases h31 : n ≤ 27132
  · exact ⟨27061, by norm_num, by omega, by omega⟩
  by_cases h32 : n ≤ 27198
  · exact ⟨27127, by norm_num, by omega, by omega⟩
  by_cases h33 : n ≤ 27268
  · exact ⟨27197, by norm_num, by omega, by omega⟩
  by_cases h34 : n ≤ 27330
  · exact ⟨27259, by norm_num, by omega, by omega⟩
  by_cases h35 : n ≤ 27400
  · exact ⟨27329, by norm_num, by omega, by omega⟩
  by_cases h36 : n ≤ 27468
  · exact ⟨27397, by norm_num, by omega, by omega⟩
  · exact ⟨27457, by norm_num, by omega, by omega⟩

set_option maxHeartbeats 800000 in
