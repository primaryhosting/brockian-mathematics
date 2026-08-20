import Mathlib
import SylvesterSchurCore
namespace Brockian.SylvesterSchur
/-- Sylvester–Schur: for n > k ≥ 1, some element of {n+1,…,n+k} has a prime factor > k. -/

lemma exists_prime_sub_72_block_34 (n : ℕ) (hlo : 85001 ≤ n) (hhi : n ≤ 87500) :
    ∃ p : ℕ, p.Prime ∧ n - 72 < p ∧ p ≤ n := by
  by_cases h0 : n ≤ 85062
  · exact ⟨84991, by norm_num, by omega, by omega⟩
  by_cases h1 : n ≤ 85132
  · exact ⟨85061, by norm_num, by omega, by omega⟩
  by_cases h2 : n ≤ 85204
  · exact ⟨85133, by norm_num, by omega, by omega⟩
  by_cases h3 : n ≤ 85272
  · exact ⟨85201, by norm_num, by omega, by omega⟩
  by_cases h4 : n ≤ 85330
  · exact ⟨85259, by norm_num, by omega, by omega⟩
  by_cases h5 : n ≤ 85402
  · exact ⟨85331, by norm_num, by omega, by omega⟩
  by_cases h6 : n ≤ 85452
  · exact ⟨85381, by norm_num, by omega, by omega⟩
  by_cases h7 : n ≤ 85524
  · exact ⟨85453, by norm_num, by omega, by omega⟩
  by_cases h8 : n ≤ 85594
  · exact ⟨85523, by norm_num, by omega, by omega⟩
  by_cases h9 : n ≤ 85648
  · exact ⟨85577, by norm_num, by omega, by omega⟩
  by_cases h10 : n ≤ 85714
  · exact ⟨85643, by norm_num, by omega, by omega⟩
  by_cases h11 : n ≤ 85782
  · exact ⟨85711, by norm_num, by omega, by omega⟩
  by_cases h12 : n ≤ 85852
  · exact ⟨85781, by norm_num, by omega, by omega⟩
  by_cases h13 : n ≤ 85924
  · exact ⟨85853, by norm_num, by omega, by omega⟩
  by_cases h14 : n ≤ 85980
  · exact ⟨85909, by norm_num, by omega, by omega⟩
  by_cases h15 : n ≤ 86004
  · exact ⟨85933, by norm_num, by omega, by omega⟩
  by_cases h16 : n ≤ 86070
  · exact ⟨85999, by norm_num, by omega, by omega⟩
  by_cases h17 : n ≤ 86140
  · exact ⟨86069, by norm_num, by omega, by omega⟩
  by_cases h18 : n ≤ 86208
  · exact ⟨86137, by norm_num, by omega, by omega⟩
  by_cases h19 : n ≤ 86280
  · exact ⟨86209, by norm_num, by omega, by omega⟩
  by_cases h20 : n ≤ 86340
  · exact ⟨86269, by norm_num, by omega, by omega⟩
  by_cases h21 : n ≤ 86412
  · exact ⟨86341, by norm_num, by omega, by omega⟩
  by_cases h22 : n ≤ 86484
  · exact ⟨86413, by norm_num, by omega, by omega⟩
  by_cases h23 : n ≤ 86548
  · exact ⟨86477, by norm_num, by omega, by omega⟩
  by_cases h24 : n ≤ 86610
  · exact ⟨86539, by norm_num, by omega, by omega⟩
  by_cases h25 : n ≤ 86670
  · exact ⟨86599, by norm_num, by omega, by omega⟩
  by_cases h26 : n ≤ 86700
  · exact ⟨86629, by norm_num, by omega, by omega⟩
  by_cases h27 : n ≤ 86764
  · exact ⟨86693, by norm_num, by omega, by omega⟩
  by_cases h28 : n ≤ 86824
  · exact ⟨86753, by norm_num, by omega, by omega⟩
  by_cases h29 : n ≤ 86884
  · exact ⟨86813, by norm_num, by omega, by omega⟩
  by_cases h30 : n ≤ 86940
  · exact ⟨86869, by norm_num, by omega, by omega⟩
  by_cases h31 : n ≤ 87010
  · exact ⟨86939, by norm_num, by omega, by omega⟩
  by_cases h32 : n ≤ 87082
  · exact ⟨87011, by norm_num, by omega, by omega⟩
  by_cases h33 : n ≤ 87154
  · exact ⟨87083, by norm_num, by omega, by omega⟩
  by_cases h34 : n ≤ 87222
  · exact ⟨87151, by norm_num, by omega, by omega⟩
  by_cases h35 : n ≤ 87294
  · exact ⟨87223, by norm_num, by omega, by omega⟩
  by_cases h36 : n ≤ 87364
  · exact ⟨87293, by norm_num, by omega, by omega⟩
  by_cases h37 : n ≤ 87430
  · exact ⟨87359, by norm_num, by omega, by omega⟩
  by_cases h38 : n ≤ 87498
  · exact ⟨87427, by norm_num, by omega, by omega⟩
  · exact ⟨87491, by norm_num, by omega, by omega⟩

set_option maxHeartbeats 800000 in
