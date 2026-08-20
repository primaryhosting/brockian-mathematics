import Mathlib
import SylvesterSchurCore
namespace Brockian.SylvesterSchur
/-- Sylvester–Schur: for n > k ≥ 1, some element of {n+1,…,n+k} has a prime factor > k. -/

lemma exists_prime_sub_72_block_45 (n : ℕ) (hlo : 112501 ≤ n) (hhi : n ≤ 115000) :
    ∃ p : ℕ, p.Prime ∧ n - 72 < p ∧ p ≤ n := by
  by_cases h0 : n ≤ 112572
  · exact ⟨112501, by norm_num, by omega, by omega⟩
  by_cases h1 : n ≤ 112644
  · exact ⟨112573, by norm_num, by omega, by omega⟩
  by_cases h2 : n ≤ 112714
  · exact ⟨112643, by norm_num, by omega, by omega⟩
  by_cases h3 : n ≤ 112762
  · exact ⟨112691, by norm_num, by omega, by omega⟩
  by_cases h4 : n ≤ 112830
  · exact ⟨112759, by norm_num, by omega, by omega⟩
  by_cases h5 : n ≤ 112902
  · exact ⟨112831, by norm_num, by omega, by omega⟩
  by_cases h6 : n ≤ 112972
  · exact ⟨112901, by norm_num, by omega, by omega⟩
  by_cases h7 : n ≤ 113038
  · exact ⟨112967, by norm_num, by omega, by omega⟩
  by_cases h8 : n ≤ 113110
  · exact ⟨113039, by norm_num, by omega, by omega⟩
  by_cases h9 : n ≤ 113182
  · exact ⟨113111, by norm_num, by omega, by omega⟩
  by_cases h10 : n ≤ 113248
  · exact ⟨113177, by norm_num, by omega, by omega⟩
  by_cases h11 : n ≤ 113304
  · exact ⟨113233, by norm_num, by omega, by omega⟩
  by_cases h12 : n ≤ 113358
  · exact ⟨113287, by norm_num, by omega, by omega⟩
  by_cases h13 : n ≤ 113430
  · exact ⟨113359, by norm_num, by omega, by omega⟩
  by_cases h14 : n ≤ 113488
  · exact ⟨113417, by norm_num, by omega, by omega⟩
  by_cases h15 : n ≤ 113560
  · exact ⟨113489, by norm_num, by omega, by omega⟩
  by_cases h16 : n ≤ 113628
  · exact ⟨113557, by norm_num, by omega, by omega⟩
  by_cases h17 : n ≤ 113694
  · exact ⟨113623, by norm_num, by omega, by omega⟩
  by_cases h18 : n ≤ 113754
  · exact ⟨113683, by norm_num, by omega, by omega⟩
  by_cases h19 : n ≤ 113820
  · exact ⟨113749, by norm_num, by omega, by omega⟩
  by_cases h20 : n ≤ 113890
  · exact ⟨113819, by norm_num, by omega, by omega⟩
  by_cases h21 : n ≤ 113962
  · exact ⟨113891, by norm_num, by omega, by omega⟩
  by_cases h22 : n ≤ 114034
  · exact ⟨113963, by norm_num, by omega, by omega⟩
  by_cases h23 : n ≤ 114102
  · exact ⟨114031, by norm_num, by omega, by omega⟩
  by_cases h24 : n ≤ 114160
  · exact ⟨114089, by norm_num, by omega, by omega⟩
  by_cases h25 : n ≤ 114232
  · exact ⟨114161, by norm_num, by omega, by omega⟩
  by_cases h26 : n ≤ 114300
  · exact ⟨114229, by norm_num, by omega, by omega⟩
  by_cases h27 : n ≤ 114370
  · exact ⟨114299, by norm_num, by omega, by omega⟩
  by_cases h28 : n ≤ 114442
  · exact ⟨114371, by norm_num, by omega, by omega⟩
  by_cases h29 : n ≤ 114490
  · exact ⟨114419, by norm_num, by omega, by omega⟩
  by_cases h30 : n ≤ 114558
  · exact ⟨114487, by norm_num, by omega, by omega⟩
  by_cases h31 : n ≤ 114624
  · exact ⟨114553, by norm_num, by omega, by omega⟩
  by_cases h32 : n ≤ 114688
  · exact ⟨114617, by norm_num, by omega, by omega⟩
  by_cases h33 : n ≤ 114760
  · exact ⟨114689, by norm_num, by omega, by omega⟩
  by_cases h34 : n ≤ 114832
  · exact ⟨114761, by norm_num, by omega, by omega⟩
  by_cases h35 : n ≤ 114904
  · exact ⟨114833, by norm_num, by omega, by omega⟩
  by_cases h36 : n ≤ 114972
  · exact ⟨114901, by norm_num, by omega, by omega⟩
  · exact ⟨114973, by norm_num, by omega, by omega⟩

set_option maxHeartbeats 800000 in
