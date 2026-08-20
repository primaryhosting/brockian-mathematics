import Mathlib
import SylvesterSchurCore
namespace Brockian.SylvesterSchur
/-- Sylvester–Schur: for n > k ≥ 1, some element of {n+1,…,n+k} has a prime factor > k. -/

lemma exists_prime_sub_72_block_30 (n : ℕ) (hlo : 75001 ≤ n) (hhi : n ≤ 77500) :
    ∃ p : ℕ, p.Prime ∧ n - 72 < p ∧ p ≤ n := by
  by_cases h0 : n ≤ 75030
  · exact ⟨74959, by norm_num, by omega, by omega⟩
  by_cases h1 : n ≤ 75100
  · exact ⟨75029, by norm_num, by omega, by omega⟩
  by_cases h2 : n ≤ 75154
  · exact ⟨75083, by norm_num, by omega, by omega⟩
  by_cases h3 : n ≤ 75220
  · exact ⟨75149, by norm_num, by omega, by omega⟩
  by_cases h4 : n ≤ 75288
  · exact ⟨75217, by norm_num, by omega, by omega⟩
  by_cases h5 : n ≤ 75360
  · exact ⟨75289, by norm_num, by omega, by omega⟩
  by_cases h6 : n ≤ 75424
  · exact ⟨75353, by norm_num, by omega, by omega⟩
  by_cases h7 : n ≤ 75478
  · exact ⟨75407, by norm_num, by omega, by omega⟩
  by_cases h8 : n ≤ 75550
  · exact ⟨75479, by norm_num, by omega, by omega⟩
  by_cases h9 : n ≤ 75612
  · exact ⟨75541, by norm_num, by omega, by omega⟩
  by_cases h10 : n ≤ 75682
  · exact ⟨75611, by norm_num, by omega, by omega⟩
  by_cases h11 : n ≤ 75754
  · exact ⟨75683, by norm_num, by omega, by omega⟩
  by_cases h12 : n ≤ 75814
  · exact ⟨75743, by norm_num, by omega, by omega⟩
  by_cases h13 : n ≤ 75868
  · exact ⟨75797, by norm_num, by omega, by omega⟩
  by_cases h14 : n ≤ 75940
  · exact ⟨75869, by norm_num, by omega, by omega⟩
  by_cases h15 : n ≤ 76012
  · exact ⟨75941, by norm_num, by omega, by omega⟩
  by_cases h16 : n ≤ 76074
  · exact ⟨76003, by norm_num, by omega, by omega⟩
  by_cases h17 : n ≤ 76110
  · exact ⟨76039, by norm_num, by omega, by omega⟩
  by_cases h18 : n ≤ 76174
  · exact ⟨76103, by norm_num, by omega, by omega⟩
  by_cases h19 : n ≤ 76234
  · exact ⟨76163, by norm_num, by omega, by omega⟩
  by_cases h20 : n ≤ 76302
  · exact ⟨76231, by norm_num, by omega, by omega⟩
  by_cases h21 : n ≤ 76374
  · exact ⟨76303, by norm_num, by omega, by omega⟩
  by_cases h22 : n ≤ 76440
  · exact ⟨76369, by norm_num, by omega, by omega⟩
  by_cases h23 : n ≤ 76512
  · exact ⟨76441, by norm_num, by omega, by omega⟩
  by_cases h24 : n ≤ 76582
  · exact ⟨76511, by norm_num, by omega, by omega⟩
  by_cases h25 : n ≤ 76650
  · exact ⟨76579, by norm_num, by omega, by omega⟩
  by_cases h26 : n ≤ 76722
  · exact ⟨76651, by norm_num, by omega, by omega⟩
  by_cases h27 : n ≤ 76788
  · exact ⟨76717, by norm_num, by omega, by omega⟩
  by_cases h28 : n ≤ 76852
  · exact ⟨76781, by norm_num, by omega, by omega⟩
  by_cases h29 : n ≤ 76918
  · exact ⟨76847, by norm_num, by omega, by omega⟩
  by_cases h30 : n ≤ 76990
  · exact ⟨76919, by norm_num, by omega, by omega⟩
  by_cases h31 : n ≤ 77062
  · exact ⟨76991, by norm_num, by omega, by omega⟩
  by_cases h32 : n ≤ 77118
  · exact ⟨77047, by norm_num, by omega, by omega⟩
  by_cases h33 : n ≤ 77172
  · exact ⟨77101, by norm_num, by omega, by omega⟩
  by_cases h34 : n ≤ 77242
  · exact ⟨77171, by norm_num, by omega, by omega⟩
  by_cases h35 : n ≤ 77314
  · exact ⟨77243, by norm_num, by omega, by omega⟩
  by_cases h36 : n ≤ 77362
  · exact ⟨77291, by norm_num, by omega, by omega⟩
  by_cases h37 : n ≤ 77430
  · exact ⟨77359, by norm_num, by omega, by omega⟩
  · exact ⟨77431, by norm_num, by omega, by omega⟩

set_option maxHeartbeats 800000 in
