import Mathlib
import SylvesterSchurCore
namespace Brockian.SylvesterSchur
/-- Sylvester–Schur: for n > k ≥ 1, some element of {n+1,…,n+k} has a prime factor > k. -/

lemma exists_prime_sub_72_block_29 (n : ℕ) (hlo : 72501 ≤ n) (hhi : n ≤ 75000) :
    ∃ p : ℕ, p.Prime ∧ n - 72 < p ∧ p ≤ n := by
  by_cases h0 : n ≤ 72568
  · exact ⟨72497, by norm_num, by omega, by omega⟩
  by_cases h1 : n ≤ 72630
  · exact ⟨72559, by norm_num, by omega, by omega⟩
  by_cases h2 : n ≤ 72694
  · exact ⟨72623, by norm_num, by omega, by omega⟩
  by_cases h3 : n ≤ 72760
  · exact ⟨72689, by norm_num, by omega, by omega⟩
  by_cases h4 : n ≤ 72810
  · exact ⟨72739, by norm_num, by omega, by omega⟩
  by_cases h5 : n ≤ 72868
  · exact ⟨72797, by norm_num, by omega, by omega⟩
  by_cases h6 : n ≤ 72940
  · exact ⟨72869, by norm_num, by omega, by omega⟩
  by_cases h7 : n ≤ 73008
  · exact ⟨72937, by norm_num, by omega, by omega⟩
  by_cases h8 : n ≤ 73080
  · exact ⟨73009, by norm_num, by omega, by omega⟩
  by_cases h9 : n ≤ 73150
  · exact ⟨73079, by norm_num, by omega, by omega⟩
  by_cases h10 : n ≤ 73212
  · exact ⟨73141, by norm_num, by omega, by omega⟩
  by_cases h11 : n ≤ 73260
  · exact ⟨73189, by norm_num, by omega, by omega⟩
  by_cases h12 : n ≤ 73330
  · exact ⟨73259, by norm_num, by omega, by omega⟩
  by_cases h13 : n ≤ 73402
  · exact ⟨73331, by norm_num, by omega, by omega⟩
  by_cases h14 : n ≤ 73458
  · exact ⟨73387, by norm_num, by omega, by omega⟩
  by_cases h15 : n ≤ 73530
  · exact ⟨73459, by norm_num, by omega, by omega⟩
  by_cases h16 : n ≤ 73600
  · exact ⟨73529, by norm_num, by omega, by omega⟩
  by_cases h17 : n ≤ 73668
  · exact ⟨73597, by norm_num, by omega, by omega⟩
  by_cases h18 : n ≤ 73722
  · exact ⟨73651, by norm_num, by omega, by omega⟩
  by_cases h19 : n ≤ 73792
  · exact ⟨73721, by norm_num, by omega, by omega⟩
  by_cases h20 : n ≤ 73854
  · exact ⟨73783, by norm_num, by omega, by omega⟩
  by_cases h21 : n ≤ 73920
  · exact ⟨73849, by norm_num, by omega, by omega⟩
  by_cases h22 : n ≤ 73978
  · exact ⟨73907, by norm_num, by omega, by omega⟩
  by_cases h23 : n ≤ 74044
  · exact ⟨73973, by norm_num, by omega, by omega⟩
  by_cases h24 : n ≤ 74098
  · exact ⟨74027, by norm_num, by omega, by omega⟩
  by_cases h25 : n ≤ 74170
  · exact ⟨74099, by norm_num, by omega, by omega⟩
  by_cases h26 : n ≤ 74238
  · exact ⟨74167, by norm_num, by omega, by omega⟩
  by_cases h27 : n ≤ 74302
  · exact ⟨74231, by norm_num, by omega, by omega⟩
  by_cases h28 : n ≤ 74368
  · exact ⟨74297, by norm_num, by omega, by omega⟩
  by_cases h29 : n ≤ 74434
  · exact ⟨74363, by norm_num, by omega, by omega⟩
  by_cases h30 : n ≤ 74490
  · exact ⟨74419, by norm_num, by omega, by omega⟩
  by_cases h31 : n ≤ 74560
  · exact ⟨74489, by norm_num, by omega, by omega⟩
  by_cases h32 : n ≤ 74632
  · exact ⟨74561, by norm_num, by omega, by omega⟩
  by_cases h33 : n ≤ 74694
  · exact ⟨74623, by norm_num, by omega, by omega⟩
  by_cases h34 : n ≤ 74758
  · exact ⟨74687, by norm_num, by omega, by omega⟩
  by_cases h35 : n ≤ 74830
  · exact ⟨74759, by norm_num, by omega, by omega⟩
  by_cases h36 : n ≤ 74902
  · exact ⟨74831, by norm_num, by omega, by omega⟩
  by_cases h37 : n ≤ 74974
  · exact ⟨74903, by norm_num, by omega, by omega⟩
  · exact ⟨74959, by norm_num, by omega, by omega⟩

set_option maxHeartbeats 800000 in
