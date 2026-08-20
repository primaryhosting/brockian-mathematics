import Mathlib
import SylvesterSchurCore
namespace Brockian.SylvesterSchur
/-- Sylvester–Schur: for n > k ≥ 1, some element of {n+1,…,n+k} has a prime factor > k. -/

lemma exists_prime_sub_72_block_5 (n : ℕ) (hlo : 12501 ≤ n) (hhi : n ≤ 15000) :
    ∃ p : ℕ, p.Prime ∧ n - 72 < p ∧ p ≤ n := by
  by_cases h0 : n ≤ 12568
  · exact ⟨12497, by norm_num, by omega, by omega⟩
  by_cases h1 : n ≤ 12640
  · exact ⟨12569, by norm_num, by omega, by omega⟩
  by_cases h2 : n ≤ 12712
  · exact ⟨12641, by norm_num, by omega, by omega⟩
  by_cases h3 : n ≤ 12784
  · exact ⟨12713, by norm_num, by omega, by omega⟩
  by_cases h4 : n ≤ 12852
  · exact ⟨12781, by norm_num, by omega, by omega⟩
  by_cases h5 : n ≤ 12924
  · exact ⟨12853, by norm_num, by omega, by omega⟩
  by_cases h6 : n ≤ 12994
  · exact ⟨12923, by norm_num, by omega, by omega⟩
  by_cases h7 : n ≤ 13054
  · exact ⟨12983, by norm_num, by omega, by omega⟩
  by_cases h8 : n ≤ 13120
  · exact ⟨13049, by norm_num, by omega, by omega⟩
  by_cases h9 : n ≤ 13192
  · exact ⟨13121, by norm_num, by omega, by omega⟩
  by_cases h10 : n ≤ 13258
  · exact ⟨13187, by norm_num, by omega, by omega⟩
  by_cases h11 : n ≤ 13330
  · exact ⟨13259, by norm_num, by omega, by omega⟩
  by_cases h12 : n ≤ 13402
  · exact ⟨13331, by norm_num, by omega, by omega⟩
  by_cases h13 : n ≤ 13470
  · exact ⟨13399, by norm_num, by omega, by omega⟩
  by_cases h14 : n ≤ 13540
  · exact ⟨13469, by norm_num, by omega, by omega⟩
  by_cases h15 : n ≤ 13608
  · exact ⟨13537, by norm_num, by omega, by omega⟩
  by_cases h16 : n ≤ 13668
  · exact ⟨13597, by norm_num, by omega, by omega⟩
  by_cases h17 : n ≤ 13740
  · exact ⟨13669, by norm_num, by omega, by omega⟩
  by_cases h18 : n ≤ 13800
  · exact ⟨13729, by norm_num, by omega, by omega⟩
  by_cases h19 : n ≤ 13870
  · exact ⟨13799, by norm_num, by omega, by omega⟩
  by_cases h20 : n ≤ 13930
  · exact ⟨13859, by norm_num, by omega, by omega⟩
  by_cases h21 : n ≤ 14002
  · exact ⟨13931, by norm_num, by omega, by omega⟩
  by_cases h22 : n ≤ 14070
  · exact ⟨13999, by norm_num, by omega, by omega⟩
  by_cases h23 : n ≤ 14142
  · exact ⟨14071, by norm_num, by omega, by omega⟩
  by_cases h24 : n ≤ 14214
  · exact ⟨14143, by norm_num, by omega, by omega⟩
  by_cases h25 : n ≤ 14278
  · exact ⟨14207, by norm_num, by omega, by omega⟩
  by_cases h26 : n ≤ 14322
  · exact ⟨14251, by norm_num, by omega, by omega⟩
  by_cases h27 : n ≤ 14394
  · exact ⟨14323, by norm_num, by omega, by omega⟩
  by_cases h28 : n ≤ 14460
  · exact ⟨14389, by norm_num, by omega, by omega⟩
  by_cases h29 : n ≤ 14532
  · exact ⟨14461, by norm_num, by omega, by omega⟩
  by_cases h30 : n ≤ 14604
  · exact ⟨14533, by norm_num, by omega, by omega⟩
  by_cases h31 : n ≤ 14664
  · exact ⟨14593, by norm_num, by omega, by omega⟩
  by_cases h32 : n ≤ 14728
  · exact ⟨14657, by norm_num, by omega, by omega⟩
  by_cases h33 : n ≤ 14794
  · exact ⟨14723, by norm_num, by omega, by omega⟩
  by_cases h34 : n ≤ 14854
  · exact ⟨14783, by norm_num, by omega, by omega⟩
  by_cases h35 : n ≤ 14922
  · exact ⟨14851, by norm_num, by omega, by omega⟩
  by_cases h36 : n ≤ 14994
  · exact ⟨14923, by norm_num, by omega, by omega⟩
  · exact ⟨14983, by norm_num, by omega, by omega⟩

set_option maxHeartbeats 800000 in
