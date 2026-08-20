import Mathlib
import SylvesterSchurCore
namespace Brockian.SylvesterSchur
/-- Sylvester–Schur: for n > k ≥ 1, some element of {n+1,…,n+k} has a prime factor > k. -/

lemma exists_prime_sub_72_block_12 (n : ℕ) (hlo : 30001 ≤ n) (hhi : n ≤ 32500) :
    ∃ p : ℕ, p.Prime ∧ n - 72 < p ∧ p ≤ n := by
  by_cases h0 : n ≤ 30060
  · exact ⟨29989, by norm_num, by omega, by omega⟩
  by_cases h1 : n ≤ 30130
  · exact ⟨30059, by norm_num, by omega, by omega⟩
  by_cases h2 : n ≤ 30190
  · exact ⟨30119, by norm_num, by omega, by omega⟩
  by_cases h3 : n ≤ 30258
  · exact ⟨30187, by norm_num, by omega, by omega⟩
  by_cases h4 : n ≤ 30330
  · exact ⟨30259, by norm_num, by omega, by omega⟩
  by_cases h5 : n ≤ 30394
  · exact ⟨30323, by norm_num, by omega, by omega⟩
  by_cases h6 : n ≤ 30462
  · exact ⟨30391, by norm_num, by omega, by omega⟩
  by_cases h7 : n ≤ 30520
  · exact ⟨30449, by norm_num, by omega, by omega⟩
  by_cases h8 : n ≤ 30588
  · exact ⟨30517, by norm_num, by omega, by omega⟩
  by_cases h9 : n ≤ 30648
  · exact ⟨30577, by norm_num, by omega, by omega⟩
  by_cases h10 : n ≤ 30720
  · exact ⟨30649, by norm_num, by omega, by omega⟩
  by_cases h11 : n ≤ 30784
  · exact ⟨30713, by norm_num, by omega, by omega⟩
  by_cases h12 : n ≤ 30852
  · exact ⟨30781, by norm_num, by omega, by omega⟩
  by_cases h13 : n ≤ 30924
  · exact ⟨30853, by norm_num, by omega, by omega⟩
  by_cases h14 : n ≤ 30982
  · exact ⟨30911, by norm_num, by omega, by omega⟩
  by_cases h15 : n ≤ 31054
  · exact ⟨30983, by norm_num, by omega, by omega⟩
  by_cases h16 : n ≤ 31122
  · exact ⟨31051, by norm_num, by omega, by omega⟩
  by_cases h17 : n ≤ 31194
  · exact ⟨31123, by norm_num, by omega, by omega⟩
  by_cases h18 : n ≤ 31264
  · exact ⟨31193, by norm_num, by omega, by omega⟩
  by_cases h19 : n ≤ 31330
  · exact ⟨31259, by norm_num, by omega, by omega⟩
  by_cases h20 : n ≤ 31398
  · exact ⟨31327, by norm_num, by omega, by omega⟩
  by_cases h21 : n ≤ 31468
  · exact ⟨31397, by norm_num, by omega, by omega⟩
  by_cases h22 : n ≤ 31540
  · exact ⟨31469, by norm_num, by omega, by omega⟩
  by_cases h23 : n ≤ 31612
  · exact ⟨31541, by norm_num, by omega, by omega⟩
  by_cases h24 : n ≤ 31678
  · exact ⟨31607, by norm_num, by omega, by omega⟩
  by_cases h25 : n ≤ 31738
  · exact ⟨31667, by norm_num, by omega, by omega⟩
  by_cases h26 : n ≤ 31800
  · exact ⟨31729, by norm_num, by omega, by omega⟩
  by_cases h27 : n ≤ 31870
  · exact ⟨31799, by norm_num, by omega, by omega⟩
  by_cases h28 : n ≤ 31930
  · exact ⟨31859, by norm_num, by omega, by omega⟩
  by_cases h29 : n ≤ 31978
  · exact ⟨31907, by norm_num, by omega, by omega⟩
  by_cases h30 : n ≤ 32044
  · exact ⟨31973, by norm_num, by omega, by omega⟩
  by_cases h31 : n ≤ 32100
  · exact ⟨32029, by norm_num, by omega, by omega⟩
  by_cases h32 : n ≤ 32170
  · exact ⟨32099, by norm_num, by omega, by omega⟩
  by_cases h33 : n ≤ 32230
  · exact ⟨32159, by norm_num, by omega, by omega⟩
  by_cases h34 : n ≤ 32284
  · exact ⟨32213, by norm_num, by omega, by omega⟩
  by_cases h35 : n ≤ 32332
  · exact ⟨32261, by norm_num, by omega, by omega⟩
  by_cases h36 : n ≤ 32398
  · exact ⟨32327, by norm_num, by omega, by omega⟩
  by_cases h37 : n ≤ 32452
  · exact ⟨32381, by norm_num, by omega, by omega⟩
  · exact ⟨32443, by norm_num, by omega, by omega⟩

set_option maxHeartbeats 800000 in
