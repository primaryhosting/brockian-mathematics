import Mathlib
import SylvesterSchurCore
namespace Brockian.SylvesterSchur
/-- Sylvester–Schur: for n > k ≥ 1, some element of {n+1,…,n+k} has a prime factor > k. -/

lemma exists_prime_sub_72_block_18 (n : ℕ) (hlo : 45001 ≤ n) (hhi : n ≤ 47500) :
    ∃ p : ℕ, p.Prime ∧ n - 72 < p ∧ p ≤ n := by
  by_cases h0 : n ≤ 45058
  · exact ⟨44987, by norm_num, by omega, by omega⟩
  by_cases h1 : n ≤ 45124
  · exact ⟨45053, by norm_num, by omega, by omega⟩
  by_cases h2 : n ≤ 45192
  · exact ⟨45121, by norm_num, by omega, by omega⟩
  by_cases h3 : n ≤ 45262
  · exact ⟨45191, by norm_num, by omega, by omega⟩
  by_cases h4 : n ≤ 45334
  · exact ⟨45263, by norm_num, by omega, by omega⟩
  by_cases h5 : n ≤ 45400
  · exact ⟨45329, by norm_num, by omega, by omega⟩
  by_cases h6 : n ≤ 45460
  · exact ⟨45389, by norm_num, by omega, by omega⟩
  by_cases h7 : n ≤ 45510
  · exact ⟨45439, by norm_num, by omega, by omega⟩
  by_cases h8 : n ≤ 45574
  · exact ⟨45503, by norm_num, by omega, by omega⟩
  by_cases h9 : n ≤ 45640
  · exact ⟨45569, by norm_num, by omega, by omega⟩
  by_cases h10 : n ≤ 45712
  · exact ⟨45641, by norm_num, by omega, by omega⟩
  by_cases h11 : n ≤ 45778
  · exact ⟨45707, by norm_num, by omega, by omega⟩
  by_cases h12 : n ≤ 45850
  · exact ⟨45779, by norm_num, by omega, by omega⟩
  by_cases h13 : n ≤ 45912
  · exact ⟨45841, by norm_num, by omega, by omega⟩
  by_cases h14 : n ≤ 45964
  · exact ⟨45893, by norm_num, by omega, by omega⟩
  by_cases h15 : n ≤ 46030
  · exact ⟨45959, by norm_num, by omega, by omega⟩
  by_cases h16 : n ≤ 46098
  · exact ⟨46027, by norm_num, by omega, by omega⟩
  by_cases h17 : n ≤ 46170
  · exact ⟨46099, by norm_num, by omega, by omega⟩
  by_cases h18 : n ≤ 46242
  · exact ⟨46171, by norm_num, by omega, by omega⟩
  by_cases h19 : n ≤ 46308
  · exact ⟨46237, by norm_num, by omega, by omega⟩
  by_cases h20 : n ≤ 46380
  · exact ⟨46309, by norm_num, by omega, by omega⟩
  by_cases h21 : n ≤ 46452
  · exact ⟨46381, by norm_num, by omega, by omega⟩
  by_cases h22 : n ≤ 46522
  · exact ⟨46451, by norm_num, by omega, by omega⟩
  by_cases h23 : n ≤ 46594
  · exact ⟨46523, by norm_num, by omega, by omega⟩
  by_cases h24 : n ≤ 46662
  · exact ⟨46591, by norm_num, by omega, by omega⟩
  by_cases h25 : n ≤ 46734
  · exact ⟨46663, by norm_num, by omega, by omega⟩
  by_cases h26 : n ≤ 46798
  · exact ⟨46727, by norm_num, by omega, by omega⟩
  by_cases h27 : n ≤ 46842
  · exact ⟨46771, by norm_num, by omega, by omega⟩
  by_cases h28 : n ≤ 46902
  · exact ⟨46831, by norm_num, by omega, by omega⟩
  by_cases h29 : n ≤ 46972
  · exact ⟨46901, by norm_num, by omega, by omega⟩
  by_cases h30 : n ≤ 47028
  · exact ⟨46957, by norm_num, by omega, by omega⟩
  by_cases h31 : n ≤ 47088
  · exact ⟨47017, by norm_num, by omega, by omega⟩
  by_cases h32 : n ≤ 47158
  · exact ⟨47087, by norm_num, by omega, by omega⟩
  by_cases h33 : n ≤ 47220
  · exact ⟨47149, by norm_num, by omega, by omega⟩
  by_cases h34 : n ≤ 47292
  · exact ⟨47221, by norm_num, by omega, by omega⟩
  by_cases h35 : n ≤ 47364
  · exact ⟨47293, by norm_num, by omega, by omega⟩
  by_cases h36 : n ≤ 47434
  · exact ⟨47363, by norm_num, by omega, by omega⟩
  · exact ⟨47431, by norm_num, by omega, by omega⟩

set_option maxHeartbeats 800000 in
