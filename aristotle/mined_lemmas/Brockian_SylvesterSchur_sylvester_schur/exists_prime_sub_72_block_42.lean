import Mathlib
import SylvesterSchurCore
namespace Brockian.SylvesterSchur
/-- Sylvester–Schur: for n > k ≥ 1, some element of {n+1,…,n+k} has a prime factor > k. -/

lemma exists_prime_sub_72_block_42 (n : ℕ) (hlo : 105001 ≤ n) (hhi : n ≤ 107500) :
    ∃ p : ℕ, p.Prime ∧ n - 72 < p ∧ p ≤ n := by
  by_cases h0 : n ≤ 105070
  · exact ⟨104999, by norm_num, by omega, by omega⟩
  by_cases h1 : n ≤ 105142
  · exact ⟨105071, by norm_num, by omega, by omega⟩
  by_cases h2 : n ≤ 105214
  · exact ⟨105143, by norm_num, by omega, by omega⟩
  by_cases h3 : n ≤ 105282
  · exact ⟨105211, by norm_num, by omega, by omega⟩
  by_cases h4 : n ≤ 105348
  · exact ⟨105277, by norm_num, by omega, by omega⟩
  by_cases h5 : n ≤ 105412
  · exact ⟨105341, by norm_num, by omega, by omega⟩
  by_cases h6 : n ≤ 105478
  · exact ⟨105407, by norm_num, by omega, by omega⟩
  by_cases h7 : n ≤ 105538
  · exact ⟨105467, by norm_num, by omega, by omega⟩
  by_cases h8 : n ≤ 105604
  · exact ⟨105533, by norm_num, by omega, by omega⟩
  by_cases h9 : n ≤ 105672
  · exact ⟨105601, by norm_num, by omega, by omega⟩
  by_cases h10 : n ≤ 105744
  · exact ⟨105673, by norm_num, by omega, by omega⟩
  by_cases h11 : n ≤ 105804
  · exact ⟨105733, by norm_num, by omega, by omega⟩
  by_cases h12 : n ≤ 105840
  · exact ⟨105769, by norm_num, by omega, by omega⟩
  by_cases h13 : n ≤ 105900
  · exact ⟨105829, by norm_num, by omega, by omega⟩
  by_cases h14 : n ≤ 105970
  · exact ⟨105899, by norm_num, by omega, by omega⟩
  by_cases h15 : n ≤ 106042
  · exact ⟨105971, by norm_num, by omega, by omega⟩
  by_cases h16 : n ≤ 106104
  · exact ⟨106033, by norm_num, by omega, by omega⟩
  by_cases h17 : n ≤ 106174
  · exact ⟨106103, by norm_num, by omega, by omega⟩
  by_cases h18 : n ≤ 106234
  · exact ⟨106163, by norm_num, by omega, by omega⟩
  by_cases h19 : n ≤ 106290
  · exact ⟨106219, by norm_num, by omega, by omega⟩
  by_cases h20 : n ≤ 106362
  · exact ⟨106291, by norm_num, by omega, by omega⟩
  by_cases h21 : n ≤ 106434
  · exact ⟨106363, by norm_num, by omega, by omega⟩
  by_cases h22 : n ≤ 106504
  · exact ⟨106433, by norm_num, by omega, by omega⟩
  by_cases h23 : n ≤ 106572
  · exact ⟨106501, by norm_num, by omega, by omega⟩
  by_cases h24 : n ≤ 106614
  · exact ⟨106543, by norm_num, by omega, by omega⟩
  by_cases h25 : n ≤ 106662
  · exact ⟨106591, by norm_num, by omega, by omega⟩
  by_cases h26 : n ≤ 106734
  · exact ⟨106663, by norm_num, by omega, by omega⟩
  by_cases h27 : n ≤ 106798
  · exact ⟨106727, by norm_num, by omega, by omega⟩
  by_cases h28 : n ≤ 106858
  · exact ⟨106787, by norm_num, by omega, by omega⟩
  by_cases h29 : n ≤ 106930
  · exact ⟨106859, by norm_num, by omega, by omega⟩
  by_cases h30 : n ≤ 106992
  · exact ⟨106921, by norm_num, by omega, by omega⟩
  by_cases h31 : n ≤ 107064
  · exact ⟨106993, by norm_num, by omega, by omega⟩
  by_cases h32 : n ≤ 107128
  · exact ⟨107057, by norm_num, by omega, by omega⟩
  by_cases h33 : n ≤ 107194
  · exact ⟨107123, by norm_num, by omega, by omega⟩
  by_cases h34 : n ≤ 107254
  · exact ⟨107183, by norm_num, by omega, by omega⟩
  by_cases h35 : n ≤ 107322
  · exact ⟨107251, by norm_num, by omega, by omega⟩
  by_cases h36 : n ≤ 107394
  · exact ⟨107323, by norm_num, by omega, by omega⟩
  by_cases h37 : n ≤ 107448
  · exact ⟨107377, by norm_num, by omega, by omega⟩
  · exact ⟨107449, by norm_num, by omega, by omega⟩

set_option maxHeartbeats 800000 in
