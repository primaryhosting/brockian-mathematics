import Mathlib
import SylvesterSchurCore
namespace Brockian.SylvesterSchur
/-- Sylvester–Schur: for n > k ≥ 1, some element of {n+1,…,n+k} has a prime factor > k. -/

lemma exists_prime_sub_72_block_48 (n : ℕ) (hlo : 120001 ≤ n) (hhi : n ≤ 122500) :
    ∃ p : ℕ, p.Prime ∧ n - 72 < p ∧ p ≤ n := by
  by_cases h0 : n ≤ 120064
  · exact ⟨119993, by norm_num, by omega, by omega⟩
  by_cases h1 : n ≤ 120120
  · exact ⟨120049, by norm_num, by omega, by omega⟩
  by_cases h2 : n ≤ 120192
  · exact ⟨120121, by norm_num, by omega, by omega⟩
  by_cases h3 : n ≤ 120264
  · exact ⟨120193, by norm_num, by omega, by omega⟩
  by_cases h4 : n ≤ 120318
  · exact ⟨120247, by norm_num, by omega, by omega⟩
  by_cases h5 : n ≤ 120390
  · exact ⟨120319, by norm_num, by omega, by omega⟩
  by_cases h6 : n ≤ 120462
  · exact ⟨120391, by norm_num, by omega, by omega⟩
  by_cases h7 : n ≤ 120502
  · exact ⟨120431, by norm_num, by omega, by omega⟩
  by_cases h8 : n ≤ 120574
  · exact ⟨120503, by norm_num, by omega, by omega⟩
  by_cases h9 : n ≤ 120640
  · exact ⟨120569, by norm_num, by omega, by omega⟩
  by_cases h10 : n ≤ 120712
  · exact ⟨120641, by norm_num, by omega, by omega⟩
  by_cases h11 : n ≤ 120784
  · exact ⟨120713, by norm_num, by omega, by omega⟩
  by_cases h12 : n ≤ 120850
  · exact ⟨120779, by norm_num, by omega, by omega⟩
  by_cases h13 : n ≤ 120922
  · exact ⟨120851, by norm_num, by omega, by omega⟩
  by_cases h14 : n ≤ 120990
  · exact ⟨120919, by norm_num, by omega, by omega⟩
  by_cases h15 : n ≤ 121048
  · exact ⟨120977, by norm_num, by omega, by omega⟩
  by_cases h16 : n ≤ 121110
  · exact ⟨121039, by norm_num, by omega, by omega⟩
  by_cases h17 : n ≤ 121152
  · exact ⟨121081, by norm_num, by omega, by omega⟩
  by_cases h18 : n ≤ 121222
  · exact ⟨121151, by norm_num, by omega, by omega⟩
  by_cases h19 : n ≤ 121260
  · exact ⟨121189, by norm_num, by omega, by omega⟩
  by_cases h20 : n ≤ 121330
  · exact ⟨121259, by norm_num, by omega, by omega⟩
  by_cases h21 : n ≤ 121398
  · exact ⟨121327, by norm_num, by omega, by omega⟩
  by_cases h22 : n ≤ 121450
  · exact ⟨121379, by norm_num, by omega, by omega⟩
  by_cases h23 : n ≤ 121518
  · exact ⟨121447, by norm_num, by omega, by omega⟩
  by_cases h24 : n ≤ 121578
  · exact ⟨121507, by norm_num, by omega, by omega⟩
  by_cases h25 : n ≤ 121650
  · exact ⟨121579, by norm_num, by omega, by omega⟩
  by_cases h26 : n ≤ 121708
  · exact ⟨121637, by norm_num, by omega, by omega⟩
  by_cases h27 : n ≤ 121768
  · exact ⟨121697, by norm_num, by omega, by omega⟩
  by_cases h28 : n ≤ 121834
  · exact ⟨121763, by norm_num, by omega, by omega⟩
  by_cases h29 : n ≤ 121860
  · exact ⟨121789, by norm_num, by omega, by omega⟩
  by_cases h30 : n ≤ 121924
  · exact ⟨121853, by norm_num, by omega, by omega⟩
  by_cases h31 : n ≤ 121992
  · exact ⟨121921, by norm_num, by omega, by omega⟩
  by_cases h32 : n ≤ 122064
  · exact ⟨121993, by norm_num, by omega, by omega⟩
  by_cases h33 : n ≤ 122124
  · exact ⟨122053, by norm_num, by omega, by omega⟩
  by_cases h34 : n ≤ 122188
  · exact ⟨122117, by norm_num, by omega, by omega⟩
  by_cases h35 : n ≤ 122244
  · exact ⟨122173, by norm_num, by omega, by omega⟩
  by_cases h36 : n ≤ 122302
  · exact ⟨122231, by norm_num, by omega, by omega⟩
  by_cases h37 : n ≤ 122370
  · exact ⟨122299, by norm_num, by omega, by omega⟩
  by_cases h38 : n ≤ 122434
  · exact ⟨122363, by norm_num, by omega, by omega⟩
  by_cases h39 : n ≤ 122472
  · exact ⟨122401, by norm_num, by omega, by omega⟩
  · exact ⟨122471, by norm_num, by omega, by omega⟩

set_option maxHeartbeats 800000 in
