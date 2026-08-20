import Mathlib
import SylvesterSchurCore
namespace Brockian.SylvesterSchur
/-- Sylvester–Schur: for n > k ≥ 1, some element of {n+1,…,n+k} has a prime factor > k. -/

lemma exists_prime_sub_72_block_22 (n : ℕ) (hlo : 55001 ≤ n) (hhi : n ≤ 57500) :
    ∃ p : ℕ, p.Prime ∧ n - 72 < p ∧ p ≤ n := by
  by_cases h0 : n ≤ 55072
  · exact ⟨55001, by norm_num, by omega, by omega⟩
  by_cases h1 : n ≤ 55144
  · exact ⟨55073, by norm_num, by omega, by omega⟩
  by_cases h2 : n ≤ 55198
  · exact ⟨55127, by norm_num, by omega, by omega⟩
  by_cases h3 : n ≤ 55242
  · exact ⟨55171, by norm_num, by omega, by omega⟩
  by_cases h4 : n ≤ 55314
  · exact ⟨55243, by norm_num, by omega, by omega⟩
  by_cases h5 : n ≤ 55384
  · exact ⟨55313, by norm_num, by omega, by omega⟩
  by_cases h6 : n ≤ 55452
  · exact ⟨55381, by norm_num, by omega, by omega⟩
  by_cases h7 : n ≤ 55512
  · exact ⟨55441, by norm_num, by omega, by omega⟩
  by_cases h8 : n ≤ 55582
  · exact ⟨55511, by norm_num, by omega, by omega⟩
  by_cases h9 : n ≤ 55650
  · exact ⟨55579, by norm_num, by omega, by omega⟩
  by_cases h10 : n ≤ 55710
  · exact ⟨55639, by norm_num, by omega, by omega⟩
  by_cases h11 : n ≤ 55782
  · exact ⟨55711, by norm_num, by omega, by omega⟩
  by_cases h12 : n ≤ 55834
  · exact ⟨55763, by norm_num, by omega, by omega⟩
  by_cases h13 : n ≤ 55900
  · exact ⟨55829, by norm_num, by omega, by omega⟩
  by_cases h14 : n ≤ 55972
  · exact ⟨55901, by norm_num, by omega, by omega⟩
  by_cases h15 : n ≤ 56038
  · exact ⟨55967, by norm_num, by omega, by omega⟩
  by_cases h16 : n ≤ 56110
  · exact ⟨56039, by norm_num, by omega, by omega⟩
  by_cases h17 : n ≤ 56172
  · exact ⟨56101, by norm_num, by omega, by omega⟩
  by_cases h18 : n ≤ 56242
  · exact ⟨56171, by norm_num, by omega, by omega⟩
  by_cases h19 : n ≤ 56310
  · exact ⟨56239, by norm_num, by omega, by omega⟩
  by_cases h20 : n ≤ 56382
  · exact ⟨56311, by norm_num, by omega, by omega⟩
  by_cases h21 : n ≤ 56454
  · exact ⟨56383, by norm_num, by omega, by omega⟩
  by_cases h22 : n ≤ 56524
  · exact ⟨56453, by norm_num, by omega, by omega⟩
  by_cases h23 : n ≤ 56590
  · exact ⟨56519, by norm_num, by omega, by omega⟩
  by_cases h24 : n ≤ 56662
  · exact ⟨56591, by norm_num, by omega, by omega⟩
  by_cases h25 : n ≤ 56734
  · exact ⟨56663, by norm_num, by omega, by omega⟩
  by_cases h26 : n ≤ 56802
  · exact ⟨56731, by norm_num, by omega, by omega⟩
  by_cases h27 : n ≤ 56854
  · exact ⟨56783, by norm_num, by omega, by omega⟩
  by_cases h28 : n ≤ 56914
  · exact ⟨56843, by norm_num, by omega, by omega⟩
  by_cases h29 : n ≤ 56982
  · exact ⟨56911, by norm_num, by omega, by omega⟩
  by_cases h30 : n ≤ 57054
  · exact ⟨56983, by norm_num, by omega, by omega⟩
  by_cases h31 : n ≤ 57118
  · exact ⟨57047, by norm_num, by omega, by omega⟩
  by_cases h32 : n ≤ 57190
  · exact ⟨57119, by norm_num, by omega, by omega⟩
  by_cases h33 : n ≤ 57262
  · exact ⟨57191, by norm_num, by omega, by omega⟩
  by_cases h34 : n ≤ 57330
  · exact ⟨57259, by norm_num, by omega, by omega⟩
  by_cases h35 : n ≤ 57402
  · exact ⟨57331, by norm_num, by omega, by omega⟩
  by_cases h36 : n ≤ 57468
  · exact ⟨57397, by norm_num, by omega, by omega⟩
  · exact ⟨57467, by norm_num, by omega, by omega⟩

set_option maxHeartbeats 800000 in
