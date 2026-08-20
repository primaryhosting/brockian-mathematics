import Mathlib
import SylvesterSchurCore
namespace Brockian.SylvesterSchur
/-- Sylvester–Schur: for n > k ≥ 1, some element of {n+1,…,n+k} has a prime factor > k. -/

lemma exists_prime_sub_72_block_24 (n : ℕ) (hlo : 60001 ≤ n) (hhi : n ≤ 62500) :
    ∃ p : ℕ, p.Prime ∧ n - 72 < p ∧ p ≤ n := by
  by_cases h0 : n ≤ 60070
  · exact ⟨59999, by norm_num, by omega, by omega⟩
  by_cases h1 : n ≤ 60112
  · exact ⟨60041, by norm_num, by omega, by omega⟩
  by_cases h2 : n ≤ 60178
  · exact ⟨60107, by norm_num, by omega, by omega⟩
  by_cases h3 : n ≤ 60240
  · exact ⟨60169, by norm_num, by omega, by omega⟩
  by_cases h4 : n ≤ 60294
  · exact ⟨60223, by norm_num, by omega, by omega⟩
  by_cases h5 : n ≤ 60364
  · exact ⟨60293, by norm_num, by omega, by omega⟩
  by_cases h6 : n ≤ 60424
  · exact ⟨60353, by norm_num, by omega, by omega⟩
  by_cases h7 : n ≤ 60484
  · exact ⟨60413, by norm_num, by omega, by omega⟩
  by_cases h8 : n ≤ 60528
  · exact ⟨60457, by norm_num, by omega, by omega⟩
  by_cases h9 : n ≤ 60598
  · exact ⟨60527, by norm_num, by omega, by omega⟩
  by_cases h10 : n ≤ 60660
  · exact ⟨60589, by norm_num, by omega, by omega⟩
  by_cases h11 : n ≤ 60732
  · exact ⟨60661, by norm_num, by omega, by omega⟩
  by_cases h12 : n ≤ 60804
  · exact ⟨60733, by norm_num, by omega, by omega⟩
  by_cases h13 : n ≤ 60864
  · exact ⟨60793, by norm_num, by omega, by omega⟩
  by_cases h14 : n ≤ 60930
  · exact ⟨60859, by norm_num, by omega, by omega⟩
  by_cases h15 : n ≤ 60994
  · exact ⟨60923, by norm_num, by omega, by omega⟩
  by_cases h16 : n ≤ 61032
  · exact ⟨60961, by norm_num, by omega, by omega⟩
  by_cases h17 : n ≤ 61102
  · exact ⟨61031, by norm_num, by omega, by omega⟩
  by_cases h18 : n ≤ 61170
  · exact ⟨61099, by norm_num, by omega, by omega⟩
  by_cases h19 : n ≤ 61240
  · exact ⟨61169, by norm_num, by omega, by omega⟩
  by_cases h20 : n ≤ 61302
  · exact ⟨61231, by norm_num, by omega, by omega⟩
  by_cases h21 : n ≤ 61368
  · exact ⟨61297, by norm_num, by omega, by omega⟩
  by_cases h22 : n ≤ 61434
  · exact ⟨61363, by norm_num, by omega, by omega⟩
  by_cases h23 : n ≤ 61488
  · exact ⟨61417, by norm_num, by omega, by omega⟩
  by_cases h24 : n ≤ 61558
  · exact ⟨61487, by norm_num, by omega, by omega⟩
  by_cases h25 : n ≤ 61630
  · exact ⟨61559, by norm_num, by omega, by omega⟩
  by_cases h26 : n ≤ 61702
  · exact ⟨61631, by norm_num, by omega, by omega⟩
  by_cases h27 : n ≤ 61774
  · exact ⟨61703, by norm_num, by omega, by omega⟩
  by_cases h28 : n ≤ 61828
  · exact ⟨61757, by norm_num, by omega, by omega⟩
  by_cases h29 : n ≤ 61890
  · exact ⟨61819, by norm_num, by omega, by omega⟩
  by_cases h30 : n ≤ 61950
  · exact ⟨61879, by norm_num, by omega, by omega⟩
  by_cases h31 : n ≤ 62020
  · exact ⟨61949, by norm_num, by omega, by omega⟩
  by_cases h32 : n ≤ 62088
  · exact ⟨62017, by norm_num, by omega, by omega⟩
  by_cases h33 : n ≤ 62152
  · exact ⟨62081, by norm_num, by omega, by omega⟩
  by_cases h34 : n ≤ 62214
  · exact ⟨62143, by norm_num, by omega, by omega⟩
  by_cases h35 : n ≤ 62284
  · exact ⟨62213, by norm_num, by omega, by omega⟩
  by_cases h36 : n ≤ 62344
  · exact ⟨62273, by norm_num, by omega, by omega⟩
  by_cases h37 : n ≤ 62398
  · exact ⟨62327, by norm_num, by omega, by omega⟩
  by_cases h38 : n ≤ 62454
  · exact ⟨62383, by norm_num, by omega, by omega⟩
  by_cases h39 : n ≤ 62494
  · exact ⟨62423, by norm_num, by omega, by omega⟩
  · exact ⟨62483, by norm_num, by omega, by omega⟩

set_option maxHeartbeats 800000 in
