import Mathlib
import SylvesterSchurCore
namespace Brockian.SylvesterSchur
/-- Sylvester–Schur: for n > k ≥ 1, some element of {n+1,…,n+k} has a prime factor > k. -/

lemma exists_prime_sub_72_block_46 (n : ℕ) (hlo : 115001 ≤ n) (hhi : n ≤ 117500) :
    ∃ p : ℕ, p.Prime ∧ n - 72 < p ∧ p ≤ n := by
  by_cases h0 : n ≤ 115072
  · exact ⟨115001, by norm_num, by omega, by omega⟩
  by_cases h1 : n ≤ 115138
  · exact ⟨115067, by norm_num, by omega, by omega⟩
  by_cases h2 : n ≤ 115204
  · exact ⟨115133, by norm_num, by omega, by omega⟩
  by_cases h3 : n ≤ 115272
  · exact ⟨115201, by norm_num, by omega, by omega⟩
  by_cases h4 : n ≤ 115330
  · exact ⟨115259, by norm_num, by omega, by omega⟩
  by_cases h5 : n ≤ 115402
  · exact ⟨115331, by norm_num, by omega, by omega⟩
  by_cases h6 : n ≤ 115470
  · exact ⟨115399, by norm_num, by omega, by omega⟩
  by_cases h7 : n ≤ 115542
  · exact ⟨115471, by norm_num, by omega, by omega⟩
  by_cases h8 : n ≤ 115594
  · exact ⟨115523, by norm_num, by omega, by omega⟩
  by_cases h9 : n ≤ 115660
  · exact ⟨115589, by norm_num, by omega, by omega⟩
  by_cases h10 : n ≤ 115728
  · exact ⟨115657, by norm_num, by omega, by omega⟩
  by_cases h11 : n ≤ 115798
  · exact ⟨115727, by norm_num, by omega, by omega⟩
  by_cases h12 : n ≤ 115864
  · exact ⟨115793, by norm_num, by omega, by omega⟩
  by_cases h13 : n ≤ 115932
  · exact ⟨115861, by norm_num, by omega, by omega⟩
  by_cases h14 : n ≤ 116004
  · exact ⟨115933, by norm_num, by omega, by omega⟩
  by_cases h15 : n ≤ 116058
  · exact ⟨115987, by norm_num, by omega, by omega⟩
  by_cases h16 : n ≤ 116118
  · exact ⟨116047, by norm_num, by omega, by omega⟩
  by_cases h17 : n ≤ 116184
  · exact ⟨116113, by norm_num, by omega, by omega⟩
  by_cases h18 : n ≤ 116248
  · exact ⟨116177, by norm_num, by omega, by omega⟩
  by_cases h19 : n ≤ 116314
  · exact ⟨116243, by norm_num, by omega, by omega⟩
  by_cases h20 : n ≤ 116364
  · exact ⟨116293, by norm_num, by omega, by omega⟩
  by_cases h21 : n ≤ 116430
  · exact ⟨116359, by norm_num, by omega, by omega⟩
  by_cases h22 : n ≤ 116494
  · exact ⟨116423, by norm_num, by omega, by omega⟩
  by_cases h23 : n ≤ 116562
  · exact ⟨116491, by norm_num, by omega, by omega⟩
  by_cases h24 : n ≤ 116620
  · exact ⟨116549, by norm_num, by omega, by omega⟩
  by_cases h25 : n ≤ 116664
  · exact ⟨116593, by norm_num, by omega, by omega⟩
  by_cases h26 : n ≤ 116734
  · exact ⟨116663, by norm_num, by omega, by omega⟩
  by_cases h27 : n ≤ 116802
  · exact ⟨116731, by norm_num, by omega, by omega⟩
  by_cases h28 : n ≤ 116874
  · exact ⟨116803, by norm_num, by omega, by omega⟩
  by_cases h29 : n ≤ 116938
  · exact ⟨116867, by norm_num, by omega, by omega⟩
  by_cases h30 : n ≤ 117004
  · exact ⟨116933, by norm_num, by omega, by omega⟩
  by_cases h31 : n ≤ 117064
  · exact ⟨116993, by norm_num, by omega, by omega⟩
  by_cases h32 : n ≤ 117124
  · exact ⟨117053, by norm_num, by omega, by omega⟩
  by_cases h33 : n ≤ 117190
  · exact ⟨117119, by norm_num, by omega, by omega⟩
  by_cases h34 : n ≤ 117262
  · exact ⟨117191, by norm_num, by omega, by omega⟩
  by_cases h35 : n ≤ 117330
  · exact ⟨117259, by norm_num, by omega, by omega⟩
  by_cases h36 : n ≤ 117402
  · exact ⟨117331, by norm_num, by omega, by omega⟩
  by_cases h37 : n ≤ 117460
  · exact ⟨117389, by norm_num, by omega, by omega⟩
  · exact ⟨117443, by norm_num, by omega, by omega⟩

set_option maxHeartbeats 800000 in
