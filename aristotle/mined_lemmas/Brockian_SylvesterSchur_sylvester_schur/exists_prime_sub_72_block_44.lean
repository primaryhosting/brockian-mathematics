import Mathlib
import SylvesterSchurCore
namespace Brockian.SylvesterSchur
/-- Sylvester–Schur: for n > k ≥ 1, some element of {n+1,…,n+k} has a prime factor > k. -/

lemma exists_prime_sub_72_block_44 (n : ℕ) (hlo : 110001 ≤ n) (hhi : n ≤ 112500) :
    ∃ p : ℕ, p.Prime ∧ n - 72 < p ∧ p ≤ n := by
  by_cases h0 : n ≤ 110058
  · exact ⟨109987, by norm_num, by omega, by omega⟩
  by_cases h1 : n ≤ 110130
  · exact ⟨110059, by norm_num, by omega, by omega⟩
  by_cases h2 : n ≤ 110200
  · exact ⟨110129, by norm_num, by omega, by omega⟩
  by_cases h3 : n ≤ 110254
  · exact ⟨110183, by norm_num, by omega, by omega⟩
  by_cases h4 : n ≤ 110322
  · exact ⟨110251, by norm_num, by omega, by omega⟩
  by_cases h5 : n ≤ 110394
  · exact ⟨110323, by norm_num, by omega, by omega⟩
  by_cases h6 : n ≤ 110430
  · exact ⟨110359, by norm_num, by omega, by omega⟩
  by_cases h7 : n ≤ 110502
  · exact ⟨110431, by norm_num, by omega, by omega⟩
  by_cases h8 : n ≤ 110574
  · exact ⟨110503, by norm_num, by omega, by omega⟩
  by_cases h9 : n ≤ 110644
  · exact ⟨110573, by norm_num, by omega, by omega⟩
  by_cases h10 : n ≤ 110712
  · exact ⟨110641, by norm_num, by omega, by omega⟩
  by_cases h11 : n ≤ 110782
  · exact ⟨110711, by norm_num, by omega, by omega⟩
  by_cases h12 : n ≤ 110848
  · exact ⟨110777, by norm_num, by omega, by omega⟩
  by_cases h13 : n ≤ 110920
  · exact ⟨110849, by norm_num, by omega, by omega⟩
  by_cases h14 : n ≤ 110992
  · exact ⟨110921, by norm_num, by omega, by omega⟩
  by_cases h15 : n ≤ 111060
  · exact ⟨110989, by norm_num, by omega, by omega⟩
  by_cases h16 : n ≤ 111124
  · exact ⟨111053, by norm_num, by omega, by omega⟩
  by_cases h17 : n ≤ 111192
  · exact ⟨111121, by norm_num, by omega, by omega⟩
  by_cases h18 : n ≤ 111262
  · exact ⟨111191, by norm_num, by omega, by omega⟩
  by_cases h19 : n ≤ 111334
  · exact ⟨111263, by norm_num, by omega, by omega⟩
  by_cases h20 : n ≤ 111394
  · exact ⟨111323, by norm_num, by omega, by omega⟩
  by_cases h21 : n ≤ 111444
  · exact ⟨111373, by norm_num, by omega, by omega⟩
  by_cases h22 : n ≤ 111514
  · exact ⟨111443, by norm_num, by omega, by omega⟩
  by_cases h23 : n ≤ 111580
  · exact ⟨111509, by norm_num, by omega, by omega⟩
  by_cases h24 : n ≤ 111652
  · exact ⟨111581, by norm_num, by omega, by omega⟩
  by_cases h25 : n ≤ 111724
  · exact ⟨111653, by norm_num, by omega, by omega⟩
  by_cases h26 : n ≤ 111792
  · exact ⟨111721, by norm_num, by omega, by omega⟩
  by_cases h27 : n ≤ 111862
  · exact ⟨111791, by norm_num, by omega, by omega⟩
  by_cases h28 : n ≤ 111934
  · exact ⟨111863, by norm_num, by omega, by omega⟩
  by_cases h29 : n ≤ 111990
  · exact ⟨111919, by norm_num, by omega, by omega⟩
  by_cases h30 : n ≤ 112048
  · exact ⟨111977, by norm_num, by omega, by omega⟩
  by_cases h31 : n ≤ 112102
  · exact ⟨112031, by norm_num, by omega, by omega⟩
  by_cases h32 : n ≤ 112174
  · exact ⟨112103, by norm_num, by omega, by omega⟩
  by_cases h33 : n ≤ 112234
  · exact ⟨112163, by norm_num, by omega, by omega⟩
  by_cases h34 : n ≤ 112294
  · exact ⟨112223, by norm_num, by omega, by omega⟩
  by_cases h35 : n ≤ 112362
  · exact ⟨112291, by norm_num, by omega, by omega⟩
  by_cases h36 : n ≤ 112434
  · exact ⟨112363, by norm_num, by omega, by omega⟩
  · exact ⟨112429, by norm_num, by omega, by omega⟩

set_option maxHeartbeats 800000 in
