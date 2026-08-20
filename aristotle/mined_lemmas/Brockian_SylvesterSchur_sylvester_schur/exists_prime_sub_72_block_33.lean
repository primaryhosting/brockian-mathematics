import Mathlib
import SylvesterSchurCore
namespace Brockian.SylvesterSchur
/-- Sylvester–Schur: for n > k ≥ 1, some element of {n+1,…,n+k} has a prime factor > k. -/

lemma exists_prime_sub_72_block_33 (n : ℕ) (hlo : 82501 ≤ n) (hhi : n ≤ 85000) :
    ∃ p : ℕ, p.Prime ∧ n - 72 < p ∧ p ≤ n := by
  by_cases h0 : n ≤ 82570
  · exact ⟨82499, by norm_num, by omega, by omega⟩
  by_cases h1 : n ≤ 82642
  · exact ⟨82571, by norm_num, by omega, by omega⟩
  by_cases h2 : n ≤ 82704
  · exact ⟨82633, by norm_num, by omega, by omega⟩
  by_cases h3 : n ≤ 82770
  · exact ⟨82699, by norm_num, by omega, by omega⟩
  by_cases h4 : n ≤ 82834
  · exact ⟨82763, by norm_num, by omega, by omega⟩
  by_cases h5 : n ≤ 82884
  · exact ⟨82813, by norm_num, by omega, by omega⟩
  by_cases h6 : n ≤ 82954
  · exact ⟨82883, by norm_num, by omega, by omega⟩
  by_cases h7 : n ≤ 83010
  · exact ⟨82939, by norm_num, by omega, by omega⟩
  by_cases h8 : n ≤ 83080
  · exact ⟨83009, by norm_num, by omega, by omega⟩
  by_cases h9 : n ≤ 83148
  · exact ⟨83077, by norm_num, by omega, by omega⟩
  by_cases h10 : n ≤ 83208
  · exact ⟨83137, by norm_num, by omega, by omega⟩
  by_cases h11 : n ≤ 83278
  · exact ⟨83207, by norm_num, by omega, by omega⟩
  by_cases h12 : n ≤ 83344
  · exact ⟨83273, by norm_num, by omega, by omega⟩
  by_cases h13 : n ≤ 83412
  · exact ⟨83341, by norm_num, by omega, by omega⟩
  by_cases h14 : n ≤ 83478
  · exact ⟨83407, by norm_num, by omega, by omega⟩
  by_cases h15 : n ≤ 83548
  · exact ⟨83477, by norm_num, by omega, by omega⟩
  by_cases h16 : n ≤ 83608
  · exact ⟨83537, by norm_num, by omega, by omega⟩
  by_cases h17 : n ≤ 83680
  · exact ⟨83609, by norm_num, by omega, by omega⟩
  by_cases h18 : n ≤ 83734
  · exact ⟨83663, by norm_num, by omega, by omega⟩
  by_cases h19 : n ≤ 83790
  · exact ⟨83719, by norm_num, by omega, by omega⟩
  by_cases h20 : n ≤ 83862
  · exact ⟨83791, by norm_num, by omega, by omega⟩
  by_cases h21 : n ≤ 83928
  · exact ⟨83857, by norm_num, by omega, by omega⟩
  by_cases h22 : n ≤ 83992
  · exact ⟨83921, by norm_num, by omega, by omega⟩
  by_cases h23 : n ≤ 84058
  · exact ⟨83987, by norm_num, by omega, by omega⟩
  by_cases h24 : n ≤ 84130
  · exact ⟨84059, by norm_num, by omega, by omega⟩
  by_cases h25 : n ≤ 84202
  · exact ⟨84131, by norm_num, by omega, by omega⟩
  by_cases h26 : n ≤ 84270
  · exact ⟨84199, by norm_num, by omega, by omega⟩
  by_cases h27 : n ≤ 84334
  · exact ⟨84263, by norm_num, by omega, by omega⟩
  by_cases h28 : n ≤ 84390
  · exact ⟨84319, by norm_num, by omega, by omega⟩
  by_cases h29 : n ≤ 84462
  · exact ⟨84391, by norm_num, by omega, by omega⟩
  by_cases h30 : n ≤ 84534
  · exact ⟨84463, by norm_num, by omega, by omega⟩
  by_cases h31 : n ≤ 84604
  · exact ⟨84533, by norm_num, by omega, by omega⟩
  by_cases h32 : n ≤ 84660
  · exact ⟨84589, by norm_num, by omega, by omega⟩
  by_cases h33 : n ≤ 84730
  · exact ⟨84659, by norm_num, by omega, by omega⟩
  by_cases h34 : n ≤ 84802
  · exact ⟨84731, by norm_num, by omega, by omega⟩
  by_cases h35 : n ≤ 84864
  · exact ⟨84793, by norm_num, by omega, by omega⟩
  by_cases h36 : n ≤ 84930
  · exact ⟨84859, by norm_num, by omega, by omega⟩
  by_cases h37 : n ≤ 84990
  · exact ⟨84919, by norm_num, by omega, by omega⟩
  · exact ⟨84991, by norm_num, by omega, by omega⟩

set_option maxHeartbeats 800000 in
