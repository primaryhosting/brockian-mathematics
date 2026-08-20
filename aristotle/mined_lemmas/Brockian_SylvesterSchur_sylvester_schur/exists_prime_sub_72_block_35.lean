import Mathlib
import SylvesterSchurCore
namespace Brockian.SylvesterSchur
/-- Sylvester–Schur: for n > k ≥ 1, some element of {n+1,…,n+k} has a prime factor > k. -/

lemma exists_prime_sub_72_block_35 (n : ℕ) (hlo : 87501 ≤ n) (hhi : n ≤ 90000) :
    ∃ p : ℕ, p.Prime ∧ n - 72 < p ∧ p ≤ n := by
  by_cases h0 : n ≤ 87562
  · exact ⟨87491, by norm_num, by omega, by omega⟩
  by_cases h1 : n ≤ 87630
  · exact ⟨87559, by norm_num, by omega, by omega⟩
  by_cases h2 : n ≤ 87702
  · exact ⟨87631, by norm_num, by omega, by omega⟩
  by_cases h3 : n ≤ 87772
  · exact ⟨87701, by norm_num, by omega, by omega⟩
  by_cases h4 : n ≤ 87838
  · exact ⟨87767, by norm_num, by omega, by omega⟩
  by_cases h5 : n ≤ 87904
  · exact ⟨87833, by norm_num, by omega, by omega⟩
  by_cases h6 : n ≤ 87958
  · exact ⟨87887, by norm_num, by omega, by omega⟩
  by_cases h7 : n ≤ 88030
  · exact ⟨87959, by norm_num, by omega, by omega⟩
  by_cases h8 : n ≤ 88090
  · exact ⟨88019, by norm_num, by omega, by omega⟩
  by_cases h9 : n ≤ 88150
  · exact ⟨88079, by norm_num, by omega, by omega⟩
  by_cases h10 : n ≤ 88200
  · exact ⟨88129, by norm_num, by omega, by omega⟩
  by_cases h11 : n ≤ 88248
  · exact ⟨88177, by norm_num, by omega, by omega⟩
  by_cases h12 : n ≤ 88312
  · exact ⟨88241, by norm_num, by omega, by omega⟩
  by_cases h13 : n ≤ 88372
  · exact ⟨88301, by norm_num, by omega, by omega⟩
  by_cases h14 : n ≤ 88410
  · exact ⟨88339, by norm_num, by omega, by omega⟩
  by_cases h15 : n ≤ 88482
  · exact ⟨88411, by norm_num, by omega, by omega⟩
  by_cases h16 : n ≤ 88542
  · exact ⟨88471, by norm_num, by omega, by omega⟩
  by_cases h17 : n ≤ 88594
  · exact ⟨88523, by norm_num, by omega, by omega⟩
  by_cases h18 : n ≤ 88662
  · exact ⟨88591, by norm_num, by omega, by omega⟩
  by_cases h19 : n ≤ 88734
  · exact ⟨88663, by norm_num, by omega, by omega⟩
  by_cases h20 : n ≤ 88800
  · exact ⟨88729, by norm_num, by omega, by omega⟩
  by_cases h21 : n ≤ 88872
  · exact ⟨88801, by norm_num, by omega, by omega⟩
  by_cases h22 : n ≤ 88944
  · exact ⟨88873, by norm_num, by omega, by omega⟩
  by_cases h23 : n ≤ 89008
  · exact ⟨88937, by norm_num, by omega, by omega⟩
  by_cases h24 : n ≤ 89080
  · exact ⟨89009, by norm_num, by omega, by omega⟩
  by_cases h25 : n ≤ 89142
  · exact ⟨89071, by norm_num, by omega, by omega⟩
  by_cases h26 : n ≤ 89208
  · exact ⟨89137, by norm_num, by omega, by omega⟩
  by_cases h27 : n ≤ 89280
  · exact ⟨89209, by norm_num, by omega, by omega⟩
  by_cases h28 : n ≤ 89344
  · exact ⟨89273, by norm_num, by omega, by omega⟩
  by_cases h29 : n ≤ 89400
  · exact ⟨89329, by norm_num, by omega, by omega⟩
  by_cases h30 : n ≤ 89470
  · exact ⟨89399, by norm_num, by omega, by omega⟩
  by_cases h31 : n ≤ 89530
  · exact ⟨89459, by norm_num, by omega, by omega⟩
  by_cases h32 : n ≤ 89598
  · exact ⟨89527, by norm_num, by omega, by omega⟩
  by_cases h33 : n ≤ 89670
  · exact ⟨89599, by norm_num, by omega, by omega⟩
  by_cases h34 : n ≤ 89742
  · exact ⟨89671, by norm_num, by omega, by omega⟩
  by_cases h35 : n ≤ 89760
  · exact ⟨89689, by norm_num, by omega, by omega⟩
  by_cases h36 : n ≤ 89830
  · exact ⟨89759, by norm_num, by omega, by omega⟩
  by_cases h37 : n ≤ 89892
  · exact ⟨89821, by norm_num, by omega, by omega⟩
  by_cases h38 : n ≤ 89962
  · exact ⟨89891, by norm_num, by omega, by omega⟩
  · exact ⟨89963, by norm_num, by omega, by omega⟩

set_option maxHeartbeats 800000 in
