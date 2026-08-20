import Mathlib
import SylvesterSchurCore
namespace Brockian.SylvesterSchur
/-- Sylvester–Schur: for n > k ≥ 1, some element of {n+1,…,n+k} has a prime factor > k. -/

lemma exists_prime_sub_72_block_43 (n : ℕ) (hlo : 107501 ≤ n) (hhi : n ≤ 110000) :
    ∃ p : ℕ, p.Prime ∧ n - 72 < p ∧ p ≤ n := by
  by_cases h0 : n ≤ 107544
  · exact ⟨107473, by norm_num, by omega, by omega⟩
  by_cases h1 : n ≤ 107580
  · exact ⟨107509, by norm_num, by omega, by omega⟩
  by_cases h2 : n ≤ 107652
  · exact ⟨107581, by norm_num, by omega, by omega⟩
  by_cases h3 : n ≤ 107718
  · exact ⟨107647, by norm_num, by omega, by omega⟩
  by_cases h4 : n ≤ 107790
  · exact ⟨107719, by norm_num, by omega, by omega⟩
  by_cases h5 : n ≤ 107862
  · exact ⟨107791, by norm_num, by omega, by omega⟩
  by_cases h6 : n ≤ 107928
  · exact ⟨107857, by norm_num, by omega, by omega⟩
  by_cases h7 : n ≤ 107998
  · exact ⟨107927, by norm_num, by omega, by omega⟩
  by_cases h8 : n ≤ 108070
  · exact ⟨107999, by norm_num, by omega, by omega⟩
  by_cases h9 : n ≤ 108132
  · exact ⟨108061, by norm_num, by omega, by omega⟩
  by_cases h10 : n ≤ 108202
  · exact ⟨108131, by norm_num, by omega, by omega⟩
  by_cases h11 : n ≤ 108274
  · exact ⟨108203, by norm_num, by omega, by omega⟩
  by_cases h12 : n ≤ 108342
  · exact ⟨108271, by norm_num, by omega, by omega⟩
  by_cases h13 : n ≤ 108414
  · exact ⟨108343, by norm_num, by omega, by omega⟩
  by_cases h14 : n ≤ 108484
  · exact ⟨108413, by norm_num, by omega, by omega⟩
  by_cases h15 : n ≤ 108534
  · exact ⟨108463, by norm_num, by omega, by omega⟩
  by_cases h16 : n ≤ 108604
  · exact ⟨108533, by norm_num, by omega, by omega⟩
  by_cases h17 : n ≤ 108658
  · exact ⟨108587, by norm_num, by omega, by omega⟩
  by_cases h18 : n ≤ 108720
  · exact ⟨108649, by norm_num, by omega, by omega⟩
  by_cases h19 : n ≤ 108780
  · exact ⟨108709, by norm_num, by omega, by omega⟩
  by_cases h20 : n ≤ 108840
  · exact ⟨108769, by norm_num, by omega, by omega⟩
  by_cases h21 : n ≤ 108898
  · exact ⟨108827, by norm_num, by omega, by omega⟩
  by_cases h22 : n ≤ 108964
  · exact ⟨108893, by norm_num, by omega, by omega⟩
  by_cases h23 : n ≤ 109032
  · exact ⟨108961, by norm_num, by omega, by omega⟩
  by_cases h24 : n ≤ 109084
  · exact ⟨109013, by norm_num, by omega, by omega⟩
  by_cases h25 : n ≤ 109144
  · exact ⟨109073, by norm_num, by omega, by omega⟩
  by_cases h26 : n ≤ 109212
  · exact ⟨109141, by norm_num, by omega, by omega⟩
  by_cases h27 : n ≤ 109282
  · exact ⟨109211, by norm_num, by omega, by omega⟩
  by_cases h28 : n ≤ 109350
  · exact ⟨109279, by norm_num, by omega, by omega⟩
  by_cases h29 : n ≤ 109402
  · exact ⟨109331, by norm_num, by omega, by omega⟩
  by_cases h30 : n ≤ 109468
  · exact ⟨109397, by norm_num, by omega, by omega⟩
  by_cases h31 : n ≤ 109540
  · exact ⟨109469, by norm_num, by omega, by omega⟩
  by_cases h32 : n ≤ 109612
  · exact ⟨109541, by norm_num, by omega, by omega⟩
  by_cases h33 : n ≤ 109680
  · exact ⟨109609, by norm_num, by omega, by omega⟩
  by_cases h34 : n ≤ 109744
  · exact ⟨109673, by norm_num, by omega, by omega⟩
  by_cases h35 : n ≤ 109812
  · exact ⟨109741, by norm_num, by omega, by omega⟩
  by_cases h36 : n ≤ 109878
  · exact ⟨109807, by norm_num, by omega, by omega⟩
  by_cases h37 : n ≤ 109944
  · exact ⟨109873, by norm_num, by omega, by omega⟩
  · exact ⟨109943, by norm_num, by omega, by omega⟩

set_option maxHeartbeats 800000 in
