import Mathlib
import SylvesterSchurCore
namespace Brockian.SylvesterSchur
/-- Sylvester–Schur: for n > k ≥ 1, some element of {n+1,…,n+k} has a prime factor > k. -/

lemma exists_prime_sub_72_block_19 (n : ℕ) (hlo : 47501 ≤ n) (hhi : n ≤ 50000) :
    ∃ p : ℕ, p.Prime ∧ n - 72 < p ∧ p ≤ n := by
  by_cases h0 : n ≤ 47572
  · exact ⟨47501, by norm_num, by omega, by omega⟩
  by_cases h1 : n ≤ 47640
  · exact ⟨47569, by norm_num, by omega, by omega⟩
  by_cases h2 : n ≤ 47710
  · exact ⟨47639, by norm_num, by omega, by omega⟩
  by_cases h3 : n ≤ 47782
  · exact ⟨47711, by norm_num, by omega, by omega⟩
  by_cases h4 : n ≤ 47850
  · exact ⟨47779, by norm_num, by omega, by omega⟩
  by_cases h5 : n ≤ 47914
  · exact ⟨47843, by norm_num, by omega, by omega⟩
  by_cases h6 : n ≤ 47982
  · exact ⟨47911, by norm_num, by omega, by omega⟩
  by_cases h7 : n ≤ 48052
  · exact ⟨47981, by norm_num, by omega, by omega⟩
  by_cases h8 : n ≤ 48120
  · exact ⟨48049, by norm_num, by omega, by omega⟩
  by_cases h9 : n ≤ 48192
  · exact ⟨48121, by norm_num, by omega, by omega⟩
  by_cases h10 : n ≤ 48264
  · exact ⟨48193, by norm_num, by omega, by omega⟩
  by_cases h11 : n ≤ 48330
  · exact ⟨48259, by norm_num, by omega, by omega⟩
  by_cases h12 : n ≤ 48384
  · exact ⟨48313, by norm_num, by omega, by omega⟩
  by_cases h13 : n ≤ 48454
  · exact ⟨48383, by norm_num, by omega, by omega⟩
  by_cases h14 : n ≤ 48520
  · exact ⟨48449, by norm_num, by omega, by omega⟩
  by_cases h15 : n ≤ 48568
  · exact ⟨48497, by norm_num, by omega, by omega⟩
  by_cases h16 : n ≤ 48634
  · exact ⟨48563, by norm_num, by omega, by omega⟩
  by_cases h17 : n ≤ 48694
  · exact ⟨48623, by norm_num, by omega, by omega⟩
  by_cases h18 : n ≤ 48750
  · exact ⟨48679, by norm_num, by omega, by omega⟩
  by_cases h19 : n ≤ 48822
  · exact ⟨48751, by norm_num, by omega, by omega⟩
  by_cases h20 : n ≤ 48894
  · exact ⟨48823, by norm_num, by omega, by omega⟩
  by_cases h21 : n ≤ 48960
  · exact ⟨48889, by norm_num, by omega, by omega⟩
  by_cases h22 : n ≤ 49024
  · exact ⟨48953, by norm_num, by omega, by omega⟩
  by_cases h23 : n ≤ 49090
  · exact ⟨49019, by norm_num, by omega, by omega⟩
  by_cases h24 : n ≤ 49152
  · exact ⟨49081, by norm_num, by omega, by omega⟩
  by_cases h25 : n ≤ 49210
  · exact ⟨49139, by norm_num, by omega, by omega⟩
  by_cases h26 : n ≤ 49282
  · exact ⟨49211, by norm_num, by omega, by omega⟩
  by_cases h27 : n ≤ 49350
  · exact ⟨49279, by norm_num, by omega, by omega⟩
  by_cases h28 : n ≤ 49410
  · exact ⟨49339, by norm_num, by omega, by omega⟩
  by_cases h29 : n ≤ 49482
  · exact ⟨49411, by norm_num, by omega, by omega⟩
  by_cases h30 : n ≤ 49552
  · exact ⟨49481, by norm_num, by omega, by omega⟩
  by_cases h31 : n ≤ 49620
  · exact ⟨49549, by norm_num, by omega, by omega⟩
  by_cases h32 : n ≤ 49684
  · exact ⟨49613, by norm_num, by omega, by omega⟩
  by_cases h33 : n ≤ 49752
  · exact ⟨49681, by norm_num, by omega, by omega⟩
  by_cases h34 : n ≤ 49818
  · exact ⟨49747, by norm_num, by omega, by omega⟩
  by_cases h35 : n ≤ 49882
  · exact ⟨49811, by norm_num, by omega, by omega⟩
  by_cases h36 : n ≤ 49948
  · exact ⟨49877, by norm_num, by omega, by omega⟩
  · exact ⟨49943, by norm_num, by omega, by omega⟩

set_option maxHeartbeats 800000 in
