import Mathlib
import SylvesterSchurCore
namespace Brockian.SylvesterSchur
/-- Sylvester–Schur: for n > k ≥ 1, some element of {n+1,…,n+k} has a prime factor > k. -/

lemma exists_prime_sub_72_block_17 (n : ℕ) (hlo : 42501 ≤ n) (hhi : n ≤ 45000) :
    ∃ p : ℕ, p.Prime ∧ n - 72 < p ∧ p ≤ n := by
  by_cases h0 : n ≤ 42570
  · exact ⟨42499, by norm_num, by omega, by omega⟩
  by_cases h1 : n ≤ 42642
  · exact ⟨42571, by norm_num, by omega, by omega⟩
  by_cases h2 : n ≤ 42714
  · exact ⟨42643, by norm_num, by omega, by omega⟩
  by_cases h3 : n ≤ 42780
  · exact ⟨42709, by norm_num, by omega, by omega⟩
  by_cases h4 : n ≤ 42844
  · exact ⟨42773, by norm_num, by omega, by omega⟩
  by_cases h5 : n ≤ 42912
  · exact ⟨42841, by norm_num, by omega, by omega⟩
  by_cases h6 : n ≤ 42972
  · exact ⟨42901, by norm_num, by omega, by omega⟩
  by_cases h7 : n ≤ 43038
  · exact ⟨42967, by norm_num, by omega, by omega⟩
  by_cases h8 : n ≤ 43108
  · exact ⟨43037, by norm_num, by omega, by omega⟩
  by_cases h9 : n ≤ 43174
  · exact ⟨43103, by norm_num, by omega, by omega⟩
  by_cases h10 : n ≤ 43230
  · exact ⟨43159, by norm_num, by omega, by omega⟩
  by_cases h11 : n ≤ 43294
  · exact ⟨43223, by norm_num, by omega, by omega⟩
  by_cases h12 : n ≤ 43362
  · exact ⟨43291, by norm_num, by omega, by omega⟩
  by_cases h13 : n ≤ 43402
  · exact ⟨43331, by norm_num, by omega, by omega⟩
  by_cases h14 : n ≤ 43474
  · exact ⟨43403, by norm_num, by omega, by omega⟩
  by_cases h15 : n ≤ 43528
  · exact ⟨43457, by norm_num, by omega, by omega⟩
  by_cases h16 : n ≤ 43588
  · exact ⟨43517, by norm_num, by omega, by omega⟩
  by_cases h17 : n ≤ 43650
  · exact ⟨43579, by norm_num, by omega, by omega⟩
  by_cases h18 : n ≤ 43722
  · exact ⟨43651, by norm_num, by omega, by omega⟩
  by_cases h19 : n ≤ 43792
  · exact ⟨43721, by norm_num, by omega, by omega⟩
  by_cases h20 : n ≤ 43864
  · exact ⟨43793, by norm_num, by omega, by omega⟩
  by_cases h21 : n ≤ 43924
  · exact ⟨43853, by norm_num, by omega, by omega⟩
  by_cases h22 : n ≤ 43984
  · exact ⟨43913, by norm_num, by omega, by omega⟩
  by_cases h23 : n ≤ 44044
  · exact ⟨43973, by norm_num, by omega, by omega⟩
  by_cases h24 : n ≤ 44112
  · exact ⟨44041, by norm_num, by omega, by omega⟩
  by_cases h25 : n ≤ 44182
  · exact ⟨44111, by norm_num, by omega, by omega⟩
  by_cases h26 : n ≤ 44250
  · exact ⟨44179, by norm_num, by omega, by omega⟩
  by_cases h27 : n ≤ 44320
  · exact ⟨44249, by norm_num, by omega, by omega⟩
  by_cases h28 : n ≤ 44364
  · exact ⟨44293, by norm_num, by omega, by omega⟩
  by_cases h29 : n ≤ 44428
  · exact ⟨44357, by norm_num, by omega, by omega⟩
  by_cases h30 : n ≤ 44488
  · exact ⟨44417, by norm_num, by omega, by omega⟩
  by_cases h31 : n ≤ 44554
  · exact ⟨44483, by norm_num, by omega, by omega⟩
  by_cases h32 : n ≤ 44620
  · exact ⟨44549, by norm_num, by omega, by omega⟩
  by_cases h33 : n ≤ 44692
  · exact ⟨44621, by norm_num, by omega, by omega⟩
  by_cases h34 : n ≤ 44758
  · exact ⟨44687, by norm_num, by omega, by omega⟩
  by_cases h35 : n ≤ 44824
  · exact ⟨44753, by norm_num, by omega, by omega⟩
  by_cases h36 : n ≤ 44890
  · exact ⟨44819, by norm_num, by omega, by omega⟩
  by_cases h37 : n ≤ 44958
  · exact ⟨44887, by norm_num, by omega, by omega⟩
  · exact ⟨44959, by norm_num, by omega, by omega⟩

set_option maxHeartbeats 800000 in
