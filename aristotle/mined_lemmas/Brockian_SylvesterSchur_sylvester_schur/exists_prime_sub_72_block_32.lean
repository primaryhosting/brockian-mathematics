import Mathlib
import SylvesterSchurCore
namespace Brockian.SylvesterSchur
/-- Sylvester–Schur: for n > k ≥ 1, some element of {n+1,…,n+k} has a prime factor > k. -/

lemma exists_prime_sub_72_block_32 (n : ℕ) (hlo : 80001 ≤ n) (hhi : n ≤ 82500) :
    ∃ p : ℕ, p.Prime ∧ n - 72 < p ∧ p ≤ n := by
  by_cases h0 : n ≤ 80070
  · exact ⟨79999, by norm_num, by omega, by omega⟩
  by_cases h1 : n ≤ 80142
  · exact ⟨80071, by norm_num, by omega, by omega⟩
  by_cases h2 : n ≤ 80212
  · exact ⟨80141, by norm_num, by omega, by omega⟩
  by_cases h3 : n ≤ 80280
  · exact ⟨80209, by norm_num, by omega, by omega⟩
  by_cases h4 : n ≤ 80350
  · exact ⟨80279, by norm_num, by omega, by omega⟩
  by_cases h5 : n ≤ 80418
  · exact ⟨80347, by norm_num, by omega, by omega⟩
  by_cases h6 : n ≤ 80478
  · exact ⟨80407, by norm_num, by omega, by omega⟩
  by_cases h7 : n ≤ 80544
  · exact ⟨80473, by norm_num, by omega, by omega⟩
  by_cases h8 : n ≤ 80608
  · exact ⟨80537, by norm_num, by omega, by omega⟩
  by_cases h9 : n ≤ 80674
  · exact ⟨80603, by norm_num, by omega, by omega⟩
  by_cases h10 : n ≤ 80742
  · exact ⟨80671, by norm_num, by omega, by omega⟩
  by_cases h11 : n ≤ 80808
  · exact ⟨80737, by norm_num, by omega, by omega⟩
  by_cases h12 : n ≤ 80880
  · exact ⟨80809, by norm_num, by omega, by omega⟩
  by_cases h13 : n ≤ 80934
  · exact ⟨80863, by norm_num, by omega, by omega⟩
  by_cases h14 : n ≤ 81004
  · exact ⟨80933, by norm_num, by omega, by omega⟩
  by_cases h15 : n ≤ 81072
  · exact ⟨81001, by norm_num, by omega, by omega⟩
  by_cases h16 : n ≤ 81142
  · exact ⟨81071, by norm_num, by omega, by omega⟩
  by_cases h17 : n ≤ 81202
  · exact ⟨81131, by norm_num, by omega, by omega⟩
  by_cases h18 : n ≤ 81274
  · exact ⟨81203, by norm_num, by omega, by omega⟩
  by_cases h19 : n ≤ 81310
  · exact ⟨81239, by norm_num, by omega, by omega⟩
  by_cases h20 : n ≤ 81378
  · exact ⟨81307, by norm_num, by omega, by omega⟩
  by_cases h21 : n ≤ 81444
  · exact ⟨81373, by norm_num, by omega, by omega⟩
  by_cases h22 : n ≤ 81510
  · exact ⟨81439, by norm_num, by omega, by omega⟩
  by_cases h23 : n ≤ 81580
  · exact ⟨81509, by norm_num, by omega, by omega⟩
  by_cases h24 : n ≤ 81640
  · exact ⟨81569, by norm_num, by omega, by omega⟩
  by_cases h25 : n ≤ 81708
  · exact ⟨81637, by norm_num, by omega, by omega⟩
  by_cases h26 : n ≤ 81778
  · exact ⟨81707, by norm_num, by omega, by omega⟩
  by_cases h27 : n ≤ 81844
  · exact ⟨81773, by norm_num, by omega, by omega⟩
  by_cases h28 : n ≤ 81910
  · exact ⟨81839, by norm_num, by omega, by omega⟩
  by_cases h29 : n ≤ 81972
  · exact ⟨81901, by norm_num, by omega, by omega⟩
  by_cases h30 : n ≤ 82044
  · exact ⟨81973, by norm_num, by omega, by omega⟩
  by_cases h31 : n ≤ 82110
  · exact ⟨82039, by norm_num, by omega, by omega⟩
  by_cases h32 : n ≤ 82144
  · exact ⟨82073, by norm_num, by omega, by omega⟩
  by_cases h33 : n ≤ 82212
  · exact ⟨82141, by norm_num, by omega, by omega⟩
  by_cases h34 : n ≤ 82278
  · exact ⟨82207, by norm_num, by omega, by omega⟩
  by_cases h35 : n ≤ 82350
  · exact ⟨82279, by norm_num, by omega, by omega⟩
  by_cases h36 : n ≤ 82422
  · exact ⟨82351, by norm_num, by omega, by omega⟩
  by_cases h37 : n ≤ 82492
  · exact ⟨82421, by norm_num, by omega, by omega⟩
  · exact ⟨82493, by norm_num, by omega, by omega⟩

set_option maxHeartbeats 800000 in
