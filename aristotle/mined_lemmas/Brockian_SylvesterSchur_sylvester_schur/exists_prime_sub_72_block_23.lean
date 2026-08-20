import Mathlib
import SylvesterSchurCore
namespace Brockian.SylvesterSchur
/-- Sylvester–Schur: for n > k ≥ 1, some element of {n+1,…,n+k} has a prime factor > k. -/

lemma exists_prime_sub_72_block_23 (n : ℕ) (hlo : 57501 ≤ n) (hhi : n ≤ 60000) :
    ∃ p : ℕ, p.Prime ∧ n - 72 < p ∧ p ≤ n := by
  by_cases h0 : n ≤ 57564
  · exact ⟨57493, by norm_num, by omega, by omega⟩
  by_cases h1 : n ≤ 57630
  · exact ⟨57559, by norm_num, by omega, by omega⟩
  by_cases h2 : n ≤ 57672
  · exact ⟨57601, by norm_num, by omega, by omega⟩
  by_cases h3 : n ≤ 57738
  · exact ⟨57667, by norm_num, by omega, by omega⟩
  by_cases h4 : n ≤ 57808
  · exact ⟨57737, by norm_num, by omega, by omega⟩
  by_cases h5 : n ≤ 57880
  · exact ⟨57809, by norm_num, by omega, by omega⟩
  by_cases h6 : n ≤ 57952
  · exact ⟨57881, by norm_num, by omega, by omega⟩
  by_cases h7 : n ≤ 58018
  · exact ⟨57947, by norm_num, by omega, by omega⟩
  by_cases h8 : n ≤ 58084
  · exact ⟨58013, by norm_num, by omega, by omega⟩
  by_cases h9 : n ≤ 58144
  · exact ⟨58073, by norm_num, by omega, by omega⟩
  by_cases h10 : n ≤ 58200
  · exact ⟨58129, by norm_num, by omega, by omega⟩
  by_cases h11 : n ≤ 58270
  · exact ⟨58199, by norm_num, by omega, by omega⟩
  by_cases h12 : n ≤ 58342
  · exact ⟨58271, by norm_num, by omega, by omega⟩
  by_cases h13 : n ≤ 58408
  · exact ⟨58337, by norm_num, by omega, by omega⟩
  by_cases h14 : n ≤ 58474
  · exact ⟨58403, by norm_num, by omega, by omega⟩
  by_cases h15 : n ≤ 58524
  · exact ⟨58453, by norm_num, by omega, by omega⟩
  by_cases h16 : n ≤ 58582
  · exact ⟨58511, by norm_num, by omega, by omega⟩
  by_cases h17 : n ≤ 58650
  · exact ⟨58579, by norm_num, by omega, by omega⟩
  by_cases h18 : n ≤ 58702
  · exact ⟨58631, by norm_num, by omega, by omega⟩
  by_cases h19 : n ≤ 58770
  · exact ⟨58699, by norm_num, by omega, by omega⟩
  by_cases h20 : n ≤ 58842
  · exact ⟨58771, by norm_num, by omega, by omega⟩
  by_cases h21 : n ≤ 58902
  · exact ⟨58831, by norm_num, by omega, by omega⟩
  by_cases h22 : n ≤ 58972
  · exact ⟨58901, by norm_num, by omega, by omega⟩
  by_cases h23 : n ≤ 59038
  · exact ⟨58967, by norm_num, by omega, by omega⟩
  by_cases h24 : n ≤ 59100
  · exact ⟨59029, by norm_num, by omega, by omega⟩
  by_cases h25 : n ≤ 59164
  · exact ⟨59093, by norm_num, by omega, by omega⟩
  by_cases h26 : n ≤ 59230
  · exact ⟨59159, by norm_num, by omega, by omega⟩
  by_cases h27 : n ≤ 59292
  · exact ⟨59221, by norm_num, by omega, by omega⟩
  by_cases h28 : n ≤ 59352
  · exact ⟨59281, by norm_num, by omega, by omega⟩
  by_cases h29 : n ≤ 59422
  · exact ⟨59351, by norm_num, by omega, by omega⟩
  by_cases h30 : n ≤ 59490
  · exact ⟨59419, by norm_num, by omega, by omega⟩
  by_cases h31 : n ≤ 59544
  · exact ⟨59473, by norm_num, by omega, by omega⟩
  by_cases h32 : n ≤ 59610
  · exact ⟨59539, by norm_num, by omega, by omega⟩
  by_cases h33 : n ≤ 59682
  · exact ⟨59611, by norm_num, by omega, by omega⟩
  by_cases h34 : n ≤ 59742
  · exact ⟨59671, by norm_num, by omega, by omega⟩
  by_cases h35 : n ≤ 59814
  · exact ⟨59743, by norm_num, by omega, by omega⟩
  by_cases h36 : n ≤ 59880
  · exact ⟨59809, by norm_num, by omega, by omega⟩
  by_cases h37 : n ≤ 59950
  · exact ⟨59879, by norm_num, by omega, by omega⟩
  · exact ⟨59951, by norm_num, by omega, by omega⟩

set_option maxHeartbeats 800000 in
