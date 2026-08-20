import Mathlib
import SylvesterSchurCore
namespace Brockian.SylvesterSchur
/-- Sylvester–Schur: for n > k ≥ 1, some element of {n+1,…,n+k} has a prime factor > k. -/

lemma exists_prime_sub_72_block_49 (n : ℕ) (hlo : 122501 ≤ n) (hhi : n ≤ 125000) :
    ∃ p : ℕ, p.Prime ∧ n - 72 < p ∧ p ≤ n := by
  by_cases h0 : n ≤ 122572
  · exact ⟨122501, by norm_num, by omega, by omega⟩
  by_cases h1 : n ≤ 122632
  · exact ⟨122561, by norm_num, by omega, by omega⟩
  by_cases h2 : n ≤ 122682
  · exact ⟨122611, by norm_num, by omega, by omega⟩
  by_cases h3 : n ≤ 122734
  · exact ⟨122663, by norm_num, by omega, by omega⟩
  by_cases h4 : n ≤ 122790
  · exact ⟨122719, by norm_num, by omega, by omega⟩
  by_cases h5 : n ≤ 122860
  · exact ⟨122789, by norm_num, by omega, by omega⟩
  by_cases h6 : n ≤ 122932
  · exact ⟨122861, by norm_num, by omega, by omega⟩
  by_cases h7 : n ≤ 123000
  · exact ⟨122929, by norm_num, by omega, by omega⟩
  by_cases h8 : n ≤ 123072
  · exact ⟨123001, by norm_num, by omega, by omega⟩
  by_cases h9 : n ≤ 123130
  · exact ⟨123059, by norm_num, by omega, by omega⟩
  by_cases h10 : n ≤ 123198
  · exact ⟨123127, by norm_num, by omega, by omega⟩
  by_cases h11 : n ≤ 123262
  · exact ⟨123191, by norm_num, by omega, by omega⟩
  by_cases h12 : n ≤ 123330
  · exact ⟨123259, by norm_num, by omega, by omega⟩
  by_cases h13 : n ≤ 123394
  · exact ⟨123323, by norm_num, by omega, by omega⟩
  by_cases h14 : n ≤ 123450
  · exact ⟨123379, by norm_num, by omega, by omega⟩
  by_cases h15 : n ≤ 123520
  · exact ⟨123449, by norm_num, by omega, by omega⟩
  by_cases h16 : n ≤ 123588
  · exact ⟨123517, by norm_num, by omega, by omega⟩
  by_cases h17 : n ≤ 123654
  · exact ⟨123583, by norm_num, by omega, by omega⟩
  by_cases h18 : n ≤ 123724
  · exact ⟨123653, by norm_num, by omega, by omega⟩
  by_cases h19 : n ≤ 123790
  · exact ⟨123719, by norm_num, by omega, by omega⟩
  by_cases h20 : n ≤ 123862
  · exact ⟨123791, by norm_num, by omega, by omega⟩
  by_cases h21 : n ≤ 123934
  · exact ⟨123863, by norm_num, by omega, by omega⟩
  by_cases h22 : n ≤ 124002
  · exact ⟨123931, by norm_num, by omega, by omega⟩
  by_cases h23 : n ≤ 124072
  · exact ⟨124001, by norm_num, by omega, by omega⟩
  by_cases h24 : n ≤ 124138
  · exact ⟨124067, by norm_num, by omega, by omega⟩
  by_cases h25 : n ≤ 124210
  · exact ⟨124139, by norm_num, by omega, by omega⟩
  by_cases h26 : n ≤ 124270
  · exact ⟨124199, by norm_num, by omega, by omega⟩
  by_cases h27 : n ≤ 124320
  · exact ⟨124249, by norm_num, by omega, by omega⟩
  by_cases h28 : n ≤ 124380
  · exact ⟨124309, by norm_num, by omega, by omega⟩
  by_cases h29 : n ≤ 124438
  · exact ⟨124367, by norm_num, by omega, by omega⟩
  by_cases h30 : n ≤ 124504
  · exact ⟨124433, by norm_num, by omega, by omega⟩
  by_cases h31 : n ≤ 124564
  · exact ⟨124493, by norm_num, by omega, by omega⟩
  by_cases h32 : n ≤ 124632
  · exact ⟨124561, by norm_num, by omega, by omega⟩
  by_cases h33 : n ≤ 124704
  · exact ⟨124633, by norm_num, by omega, by omega⟩
  by_cases h34 : n ≤ 124774
  · exact ⟨124703, by norm_num, by omega, by omega⟩
  by_cases h35 : n ≤ 124842
  · exact ⟨124771, by norm_num, by omega, by omega⟩
  by_cases h36 : n ≤ 124894
  · exact ⟨124823, by norm_num, by omega, by omega⟩
  by_cases h37 : n ≤ 124924
  · exact ⟨124853, by norm_num, by omega, by omega⟩
  by_cases h38 : n ≤ 124990
  · exact ⟨124919, by norm_num, by omega, by omega⟩
  · exact ⟨124991, by norm_num, by omega, by omega⟩

