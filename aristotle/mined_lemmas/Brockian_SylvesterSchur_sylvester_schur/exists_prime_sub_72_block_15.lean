import Mathlib
import SylvesterSchurCore
namespace Brockian.SylvesterSchur
/-- Sylvester–Schur: for n > k ≥ 1, some element of {n+1,…,n+k} has a prime factor > k. -/

lemma exists_prime_sub_72_block_15 (n : ℕ) (hlo : 37501 ≤ n) (hhi : n ≤ 40000) :
    ∃ p : ℕ, p.Prime ∧ n - 72 < p ∧ p ≤ n := by
  by_cases h0 : n ≤ 37572
  · exact ⟨37501, by norm_num, by omega, by omega⟩
  by_cases h1 : n ≤ 37644
  · exact ⟨37573, by norm_num, by omega, by omega⟩
  by_cases h2 : n ≤ 37714
  · exact ⟨37643, by norm_num, by omega, by omega⟩
  by_cases h3 : n ≤ 37770
  · exact ⟨37699, by norm_num, by omega, by omega⟩
  by_cases h4 : n ≤ 37818
  · exact ⟨37747, by norm_num, by omega, by omega⟩
  by_cases h5 : n ≤ 37884
  · exact ⟨37813, by norm_num, by omega, by omega⟩
  by_cases h6 : n ≤ 37950
  · exact ⟨37879, by norm_num, by omega, by omega⟩
  by_cases h7 : n ≤ 38022
  · exact ⟨37951, by norm_num, by omega, by omega⟩
  by_cases h8 : n ≤ 38082
  · exact ⟨38011, by norm_num, by omega, by omega⟩
  by_cases h9 : n ≤ 38154
  · exact ⟨38083, by norm_num, by omega, by omega⟩
  by_cases h10 : n ≤ 38224
  · exact ⟨38153, by norm_num, by omega, by omega⟩
  by_cases h11 : n ≤ 38290
  · exact ⟨38219, by norm_num, by omega, by omega⟩
  by_cases h12 : n ≤ 38358
  · exact ⟨38287, by norm_num, by omega, by omega⟩
  by_cases h13 : n ≤ 38422
  · exact ⟨38351, by norm_num, by omega, by omega⟩
  by_cases h14 : n ≤ 38464
  · exact ⟨38393, by norm_num, by omega, by omega⟩
  by_cases h15 : n ≤ 38532
  · exact ⟨38461, by norm_num, by omega, by omega⟩
  by_cases h16 : n ≤ 38572
  · exact ⟨38501, by norm_num, by omega, by omega⟩
  by_cases h17 : n ≤ 38640
  · exact ⟨38569, by norm_num, by omega, by omega⟩
  by_cases h18 : n ≤ 38710
  · exact ⟨38639, by norm_num, by omega, by omega⟩
  by_cases h19 : n ≤ 38782
  · exact ⟨38711, by norm_num, by omega, by omega⟩
  by_cases h20 : n ≤ 38854
  · exact ⟨38783, by norm_num, by omega, by omega⟩
  by_cases h21 : n ≤ 38922
  · exact ⟨38851, by norm_num, by omega, by omega⟩
  by_cases h22 : n ≤ 38994
  · exact ⟨38923, by norm_num, by omega, by omega⟩
  by_cases h23 : n ≤ 39064
  · exact ⟨38993, by norm_num, by omega, by omega⟩
  by_cases h24 : n ≤ 39118
  · exact ⟨39047, by norm_num, by omega, by omega⟩
  by_cases h25 : n ≤ 39190
  · exact ⟨39119, by norm_num, by omega, by omega⟩
  by_cases h26 : n ≤ 39262
  · exact ⟨39191, by norm_num, by omega, by omega⟩
  by_cases h27 : n ≤ 39322
  · exact ⟨39251, by norm_num, by omega, by omega⟩
  by_cases h28 : n ≤ 39394
  · exact ⟨39323, by norm_num, by omega, by omega⟩
  by_cases h29 : n ≤ 39454
  · exact ⟨39383, by norm_num, by omega, by omega⟩
  by_cases h30 : n ≤ 39522
  · exact ⟨39451, by norm_num, by omega, by omega⟩
  by_cases h31 : n ≤ 39592
  · exact ⟨39521, by norm_num, by omega, by omega⟩
  by_cases h32 : n ≤ 39652
  · exact ⟨39581, by norm_num, by omega, by omega⟩
  by_cases h33 : n ≤ 39702
  · exact ⟨39631, by norm_num, by omega, by omega⟩
  by_cases h34 : n ≤ 39774
  · exact ⟨39703, by norm_num, by omega, by omega⟩
  by_cases h35 : n ≤ 39840
  · exact ⟨39769, by norm_num, by omega, by omega⟩
  by_cases h36 : n ≤ 39912
  · exact ⟨39841, by norm_num, by omega, by omega⟩
  by_cases h37 : n ≤ 39972
  · exact ⟨39901, by norm_num, by omega, by omega⟩
  · exact ⟨39971, by norm_num, by omega, by omega⟩

set_option maxHeartbeats 800000 in
