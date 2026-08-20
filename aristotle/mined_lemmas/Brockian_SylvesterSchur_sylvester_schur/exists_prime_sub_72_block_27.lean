import Mathlib
import SylvesterSchurCore
namespace Brockian.SylvesterSchur
/-- Sylvester–Schur: for n > k ≥ 1, some element of {n+1,…,n+k} has a prime factor > k. -/

lemma exists_prime_sub_72_block_27 (n : ℕ) (hlo : 67501 ≤ n) (hhi : n ≤ 70000) :
    ∃ p : ℕ, p.Prime ∧ n - 72 < p ∧ p ≤ n := by
  by_cases h0 : n ≤ 67570
  · exact ⟨67499, by norm_num, by omega, by omega⟩
  by_cases h1 : n ≤ 67638
  · exact ⟨67567, by norm_num, by omega, by omega⟩
  by_cases h2 : n ≤ 67702
  · exact ⟨67631, by norm_num, by omega, by omega⟩
  by_cases h3 : n ≤ 67770
  · exact ⟨67699, by norm_num, by omega, by omega⟩
  by_cases h4 : n ≤ 67834
  · exact ⟨67763, by norm_num, by omega, by omega⟩
  by_cases h5 : n ≤ 67900
  · exact ⟨67829, by norm_num, by omega, by omega⟩
  by_cases h6 : n ≤ 67972
  · exact ⟨67901, by norm_num, by omega, by omega⟩
  by_cases h7 : n ≤ 68038
  · exact ⟨67967, by norm_num, by omega, by omega⟩
  by_cases h8 : n ≤ 68094
  · exact ⟨68023, by norm_num, by omega, by omega⟩
  by_cases h9 : n ≤ 68158
  · exact ⟨68087, by norm_num, by omega, by omega⟩
  by_cases h10 : n ≤ 68218
  · exact ⟨68147, by norm_num, by omega, by omega⟩
  by_cases h11 : n ≤ 68290
  · exact ⟨68219, by norm_num, by omega, by omega⟩
  by_cases h12 : n ≤ 68352
  · exact ⟨68281, by norm_num, by omega, by omega⟩
  by_cases h13 : n ≤ 68422
  · exact ⟨68351, by norm_num, by omega, by omega⟩
  by_cases h14 : n ≤ 68470
  · exact ⟨68399, by norm_num, by omega, by omega⟩
  by_cases h15 : n ≤ 68520
  · exact ⟨68449, by norm_num, by omega, by omega⟩
  by_cases h16 : n ≤ 68592
  · exact ⟨68521, by norm_num, by omega, by omega⟩
  by_cases h17 : n ≤ 68652
  · exact ⟨68581, by norm_num, by omega, by omega⟩
  by_cases h18 : n ≤ 68710
  · exact ⟨68639, by norm_num, by omega, by omega⟩
  by_cases h19 : n ≤ 68782
  · exact ⟨68711, by norm_num, by omega, by omega⟩
  by_cases h20 : n ≤ 68848
  · exact ⟨68777, by norm_num, by omega, by omega⟩
  by_cases h21 : n ≤ 68892
  · exact ⟨68821, by norm_num, by omega, by omega⟩
  by_cases h22 : n ≤ 68962
  · exact ⟨68891, by norm_num, by omega, by omega⟩
  by_cases h23 : n ≤ 69034
  · exact ⟨68963, by norm_num, by omega, by omega⟩
  by_cases h24 : n ≤ 69102
  · exact ⟨69031, by norm_num, by omega, by omega⟩
  by_cases h25 : n ≤ 69144
  · exact ⟨69073, by norm_num, by omega, by omega⟩
  by_cases h26 : n ≤ 69214
  · exact ⟨69143, by norm_num, by omega, by omega⟩
  by_cases h27 : n ≤ 69274
  · exact ⟨69203, by norm_num, by omega, by omega⟩
  by_cases h28 : n ≤ 69334
  · exact ⟨69263, by norm_num, by omega, by omega⟩
  by_cases h29 : n ≤ 69388
  · exact ⟨69317, by norm_num, by omega, by omega⟩
  by_cases h30 : n ≤ 69460
  · exact ⟨69389, by norm_num, by omega, by omega⟩
  by_cases h31 : n ≤ 69528
  · exact ⟨69457, by norm_num, by omega, by omega⟩
  by_cases h32 : n ≤ 69570
  · exact ⟨69499, by norm_num, by omega, by omega⟩
  by_cases h33 : n ≤ 69628
  · exact ⟨69557, by norm_num, by omega, by omega⟩
  by_cases h34 : n ≤ 69694
  · exact ⟨69623, by norm_num, by omega, by omega⟩
  by_cases h35 : n ≤ 69762
  · exact ⟨69691, by norm_num, by omega, by omega⟩
  by_cases h36 : n ≤ 69834
  · exact ⟨69763, by norm_num, by omega, by omega⟩
  by_cases h37 : n ≤ 69904
  · exact ⟨69833, by norm_num, by omega, by omega⟩
  by_cases h38 : n ≤ 69970
  · exact ⟨69899, by norm_num, by omega, by omega⟩
  · exact ⟨69959, by norm_num, by omega, by omega⟩

set_option maxHeartbeats 800000 in
