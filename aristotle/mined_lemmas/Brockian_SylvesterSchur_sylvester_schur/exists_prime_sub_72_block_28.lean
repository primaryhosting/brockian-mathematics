import Mathlib
import SylvesterSchurCore
namespace Brockian.SylvesterSchur
/-- Sylvester–Schur: for n > k ≥ 1, some element of {n+1,…,n+k} has a prime factor > k. -/

lemma exists_prime_sub_72_block_28 (n : ℕ) (hlo : 70001 ≤ n) (hhi : n ≤ 72500) :
    ∃ p : ℕ, p.Prime ∧ n - 72 < p ∧ p ≤ n := by
  by_cases h0 : n ≤ 70072
  · exact ⟨70001, by norm_num, by omega, by omega⟩
  by_cases h1 : n ≤ 70138
  · exact ⟨70067, by norm_num, by omega, by omega⟩
  by_cases h2 : n ≤ 70210
  · exact ⟨70139, by norm_num, by omega, by omega⟩
  by_cases h3 : n ≤ 70278
  · exact ⟨70207, by norm_num, by omega, by omega⟩
  by_cases h4 : n ≤ 70342
  · exact ⟨70271, by norm_num, by omega, by omega⟩
  by_cases h5 : n ≤ 70398
  · exact ⟨70327, by norm_num, by omega, by omega⟩
  by_cases h6 : n ≤ 70464
  · exact ⟨70393, by norm_num, by omega, by omega⟩
  by_cases h7 : n ≤ 70530
  · exact ⟨70459, by norm_num, by omega, by omega⟩
  by_cases h8 : n ≤ 70600
  · exact ⟨70529, by norm_num, by omega, by omega⟩
  by_cases h9 : n ≤ 70660
  · exact ⟨70589, by norm_num, by omega, by omega⟩
  by_cases h10 : n ≤ 70728
  · exact ⟨70657, by norm_num, by omega, by omega⟩
  by_cases h11 : n ≤ 70800
  · exact ⟨70729, by norm_num, by omega, by omega⟩
  by_cases h12 : n ≤ 70864
  · exact ⟨70793, by norm_num, by omega, by omega⟩
  by_cases h13 : n ≤ 70924
  · exact ⟨70853, by norm_num, by omega, by omega⟩
  by_cases h14 : n ≤ 70992
  · exact ⟨70921, by norm_num, by omega, by omega⟩
  by_cases h15 : n ≤ 71062
  · exact ⟨70991, by norm_num, by omega, by omega⟩
  by_cases h16 : n ≤ 71130
  · exact ⟨71059, by norm_num, by omega, by omega⟩
  by_cases h17 : n ≤ 71200
  · exact ⟨71129, by norm_num, by omega, by omega⟩
  by_cases h18 : n ≤ 71262
  · exact ⟨71191, by norm_num, by omega, by omega⟩
  by_cases h19 : n ≤ 71334
  · exact ⟨71263, by norm_num, by omega, by omega⟩
  by_cases h20 : n ≤ 71404
  · exact ⟨71333, by norm_num, by omega, by omega⟩
  by_cases h21 : n ≤ 71470
  · exact ⟨71399, by norm_num, by omega, by omega⟩
  by_cases h22 : n ≤ 71542
  · exact ⟨71471, by norm_num, by omega, by omega⟩
  by_cases h23 : n ≤ 71608
  · exact ⟨71537, by norm_num, by omega, by omega⟩
  by_cases h24 : n ≤ 71668
  · exact ⟨71597, by norm_num, by omega, by omega⟩
  by_cases h25 : n ≤ 71734
  · exact ⟨71663, by norm_num, by omega, by omega⟩
  by_cases h26 : n ≤ 71790
  · exact ⟨71719, by norm_num, by omega, by omega⟩
  by_cases h27 : n ≤ 71860
  · exact ⟨71789, by norm_num, by omega, by omega⟩
  by_cases h28 : n ≤ 71932
  · exact ⟨71861, by norm_num, by omega, by omega⟩
  by_cases h29 : n ≤ 72004
  · exact ⟨71933, by norm_num, by omega, by omega⟩
  by_cases h30 : n ≤ 72070
  · exact ⟨71999, by norm_num, by omega, by omega⟩
  by_cases h31 : n ≤ 72124
  · exact ⟨72053, by norm_num, by omega, by omega⟩
  by_cases h32 : n ≤ 72180
  · exact ⟨72109, by norm_num, by omega, by omega⟩
  by_cases h33 : n ≤ 72244
  · exact ⟨72173, by norm_num, by omega, by omega⟩
  by_cases h34 : n ≤ 72300
  · exact ⟨72229, by norm_num, by omega, by omega⟩
  by_cases h35 : n ≤ 72358
  · exact ⟨72287, by norm_num, by omega, by omega⟩
  by_cases h36 : n ≤ 72424
  · exact ⟨72353, by norm_num, by omega, by omega⟩
  by_cases h37 : n ≤ 72492
  · exact ⟨72421, by norm_num, by omega, by omega⟩
  · exact ⟨72493, by norm_num, by omega, by omega⟩

set_option maxHeartbeats 800000 in
