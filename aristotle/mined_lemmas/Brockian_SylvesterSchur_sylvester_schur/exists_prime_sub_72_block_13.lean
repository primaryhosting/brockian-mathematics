import Mathlib
import SylvesterSchurCore
namespace Brockian.SylvesterSchur
/-- Sylvester–Schur: for n > k ≥ 1, some element of {n+1,…,n+k} has a prime factor > k. -/

lemma exists_prime_sub_72_block_13 (n : ℕ) (hlo : 32501 ≤ n) (hhi : n ≤ 35000) :
    ∃ p : ℕ, p.Prime ∧ n - 72 < p ∧ p ≤ n := by
  by_cases h0 : n ≤ 32568
  · exact ⟨32497, by norm_num, by omega, by omega⟩
  by_cases h1 : n ≤ 32640
  · exact ⟨32569, by norm_num, by omega, by omega⟩
  by_cases h2 : n ≤ 32704
  · exact ⟨32633, by norm_num, by omega, by omega⟩
  by_cases h3 : n ≤ 32764
  · exact ⟨32693, by norm_num, by omega, by omega⟩
  by_cases h4 : n ≤ 32820
  · exact ⟨32749, by norm_num, by omega, by omega⟩
  by_cases h5 : n ≤ 32874
  · exact ⟨32803, by norm_num, by omega, by omega⟩
  by_cases h6 : n ≤ 32940
  · exact ⟨32869, by norm_num, by omega, by omega⟩
  by_cases h7 : n ≤ 33012
  · exact ⟨32941, by norm_num, by omega, by omega⟩
  by_cases h8 : n ≤ 33084
  · exact ⟨33013, by norm_num, by omega, by omega⟩
  by_cases h9 : n ≤ 33154
  · exact ⟨33083, by norm_num, by omega, by omega⟩
  by_cases h10 : n ≤ 33222
  · exact ⟨33151, by norm_num, by omega, by omega⟩
  by_cases h11 : n ≤ 33294
  · exact ⟨33223, by norm_num, by omega, by omega⟩
  by_cases h12 : n ≤ 33360
  · exact ⟨33289, by norm_num, by omega, by omega⟩
  by_cases h13 : n ≤ 33430
  · exact ⟨33359, by norm_num, by omega, by omega⟩
  by_cases h14 : n ≤ 33498
  · exact ⟨33427, by norm_num, by omega, by omega⟩
  by_cases h15 : n ≤ 33564
  · exact ⟨33493, by norm_num, by omega, by omega⟩
  by_cases h16 : n ≤ 33634
  · exact ⟨33563, by norm_num, by omega, by omega⟩
  by_cases h17 : n ≤ 33700
  · exact ⟨33629, by norm_num, by omega, by omega⟩
  by_cases h18 : n ≤ 33750
  · exact ⟨33679, by norm_num, by omega, by omega⟩
  by_cases h19 : n ≤ 33822
  · exact ⟨33751, by norm_num, by omega, by omega⟩
  by_cases h20 : n ≤ 33882
  · exact ⟨33811, by norm_num, by omega, by omega⟩
  by_cases h21 : n ≤ 33942
  · exact ⟨33871, by norm_num, by omega, by omega⟩
  by_cases h22 : n ≤ 34012
  · exact ⟨33941, by norm_num, by omega, by omega⟩
  by_cases h23 : n ≤ 34068
  · exact ⟨33997, by norm_num, by omega, by omega⟩
  by_cases h24 : n ≤ 34132
  · exact ⟨34061, by norm_num, by omega, by omega⟩
  by_cases h25 : n ≤ 34200
  · exact ⟨34129, by norm_num, by omega, by omega⟩
  by_cases h26 : n ≤ 34254
  · exact ⟨34183, by norm_num, by omega, by omega⟩
  by_cases h27 : n ≤ 34324
  · exact ⟨34253, by norm_num, by omega, by omega⟩
  by_cases h28 : n ≤ 34390
  · exact ⟨34319, by norm_num, by omega, by omega⟩
  by_cases h29 : n ≤ 34452
  · exact ⟨34381, by norm_num, by omega, by omega⟩
  by_cases h30 : n ≤ 34510
  · exact ⟨34439, by norm_num, by omega, by omega⟩
  by_cases h31 : n ≤ 34582
  · exact ⟨34511, by norm_num, by omega, by omega⟩
  by_cases h32 : n ≤ 34654
  · exact ⟨34583, by norm_num, by omega, by omega⟩
  by_cases h33 : n ≤ 34722
  · exact ⟨34651, by norm_num, by omega, by omega⟩
  by_cases h34 : n ≤ 34792
  · exact ⟨34721, by norm_num, by omega, by omega⟩
  by_cases h35 : n ≤ 34852
  · exact ⟨34781, by norm_num, by omega, by omega⟩
  by_cases h36 : n ≤ 34920
  · exact ⟨34849, by norm_num, by omega, by omega⟩
  by_cases h37 : n ≤ 34990
  · exact ⟨34919, by norm_num, by omega, by omega⟩
  · exact ⟨34981, by norm_num, by omega, by omega⟩

set_option maxHeartbeats 800000 in
