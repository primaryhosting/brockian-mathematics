import Mathlib
import SylvesterSchurCore
namespace Brockian.SylvesterSchur
/-- Sylvester–Schur: for n > k ≥ 1, some element of {n+1,…,n+k} has a prime factor > k. -/

lemma exists_prime_sub_72_block_4 (n : ℕ) (hlo : 10001 ≤ n) (hhi : n ≤ 12500) :
    ∃ p : ℕ, p.Prime ∧ n - 72 < p ∧ p ≤ n := by
  by_cases h0 : n ≤ 10044
  · exact ⟨9973, by norm_num, by omega, by omega⟩
  by_cases h1 : n ≤ 10110
  · exact ⟨10039, by norm_num, by omega, by omega⟩
  by_cases h2 : n ≤ 10182
  · exact ⟨10111, by norm_num, by omega, by omega⟩
  by_cases h3 : n ≤ 10252
  · exact ⟨10181, by norm_num, by omega, by omega⟩
  by_cases h4 : n ≤ 10324
  · exact ⟨10253, by norm_num, by omega, by omega⟩
  by_cases h5 : n ≤ 10392
  · exact ⟨10321, by norm_num, by omega, by omega⟩
  by_cases h6 : n ≤ 10462
  · exact ⟨10391, by norm_num, by omega, by omega⟩
  by_cases h7 : n ≤ 10534
  · exact ⟨10463, by norm_num, by omega, by omega⟩
  by_cases h8 : n ≤ 10602
  · exact ⟨10531, by norm_num, by omega, by omega⟩
  by_cases h9 : n ≤ 10672
  · exact ⟨10601, by norm_num, by omega, by omega⟩
  by_cases h10 : n ≤ 10738
  · exact ⟨10667, by norm_num, by omega, by omega⟩
  by_cases h11 : n ≤ 10810
  · exact ⟨10739, by norm_num, by omega, by omega⟩
  by_cases h12 : n ≤ 10870
  · exact ⟨10799, by norm_num, by omega, by omega⟩
  by_cases h13 : n ≤ 10938
  · exact ⟨10867, by norm_num, by omega, by omega⟩
  by_cases h14 : n ≤ 11010
  · exact ⟨10939, by norm_num, by omega, by omega⟩
  by_cases h15 : n ≤ 11074
  · exact ⟨11003, by norm_num, by omega, by omega⟩
  by_cases h16 : n ≤ 11142
  · exact ⟨11071, by norm_num, by omega, by omega⟩
  by_cases h17 : n ≤ 11202
  · exact ⟨11131, by norm_num, by omega, by omega⟩
  by_cases h18 : n ≤ 11268
  · exact ⟨11197, by norm_num, by omega, by omega⟩
  by_cases h19 : n ≤ 11332
  · exact ⟨11261, by norm_num, by omega, by omega⟩
  by_cases h20 : n ≤ 11400
  · exact ⟨11329, by norm_num, by omega, by omega⟩
  by_cases h21 : n ≤ 11470
  · exact ⟨11399, by norm_num, by omega, by omega⟩
  by_cases h22 : n ≤ 11542
  · exact ⟨11471, by norm_num, by omega, by omega⟩
  by_cases h23 : n ≤ 11598
  · exact ⟨11527, by norm_num, by omega, by omega⟩
  by_cases h24 : n ≤ 11668
  · exact ⟨11597, by norm_num, by omega, by omega⟩
  by_cases h25 : n ≤ 11728
  · exact ⟨11657, by norm_num, by omega, by omega⟩
  by_cases h26 : n ≤ 11790
  · exact ⟨11719, by norm_num, by omega, by omega⟩
  by_cases h27 : n ≤ 11860
  · exact ⟨11789, by norm_num, by omega, by omega⟩
  by_cases h28 : n ≤ 11910
  · exact ⟨11839, by norm_num, by omega, by omega⟩
  by_cases h29 : n ≤ 11980
  · exact ⟨11909, by norm_num, by omega, by omega⟩
  by_cases h30 : n ≤ 12052
  · exact ⟨11981, by norm_num, by omega, by omega⟩
  by_cases h31 : n ≤ 12120
  · exact ⟨12049, by norm_num, by omega, by omega⟩
  by_cases h32 : n ≤ 12190
  · exact ⟨12119, by norm_num, by omega, by omega⟩
  by_cases h33 : n ≤ 12234
  · exact ⟨12163, by norm_num, by omega, by omega⟩
  by_cases h34 : n ≤ 12298
  · exact ⟨12227, by norm_num, by omega, by omega⟩
  by_cases h35 : n ≤ 12360
  · exact ⟨12289, by norm_num, by omega, by omega⟩
  by_cases h36 : n ≤ 12418
  · exact ⟨12347, by norm_num, by omega, by omega⟩
  by_cases h37 : n ≤ 12484
  · exact ⟨12413, by norm_num, by omega, by omega⟩
  · exact ⟨12479, by norm_num, by omega, by omega⟩

set_option maxHeartbeats 800000 in
