import Mathlib
import SylvesterSchurCore
namespace Brockian.SylvesterSchur
/-- Sylvester–Schur: for n > k ≥ 1, some element of {n+1,…,n+k} has a prime factor > k. -/

lemma exists_prime_sub_72_block_21 (n : ℕ) (hlo : 52501 ≤ n) (hhi : n ≤ 55000) :
    ∃ p : ℕ, p.Prime ∧ n - 72 < p ∧ p ≤ n := by
  by_cases h0 : n ≤ 52572
  · exact ⟨52501, by norm_num, by omega, by omega⟩
  by_cases h1 : n ≤ 52642
  · exact ⟨52571, by norm_num, by omega, by omega⟩
  by_cases h2 : n ≤ 52710
  · exact ⟨52639, by norm_num, by omega, by omega⟩
  by_cases h3 : n ≤ 52782
  · exact ⟨52711, by norm_num, by omega, by omega⟩
  by_cases h4 : n ≤ 52854
  · exact ⟨52783, by norm_num, by omega, by omega⟩
  by_cases h5 : n ≤ 52908
  · exact ⟨52837, by norm_num, by omega, by omega⟩
  by_cases h6 : n ≤ 52974
  · exact ⟨52903, by norm_num, by omega, by omega⟩
  by_cases h7 : n ≤ 53044
  · exact ⟨52973, by norm_num, by omega, by omega⟩
  by_cases h8 : n ≤ 53088
  · exact ⟨53017, by norm_num, by omega, by omega⟩
  by_cases h9 : n ≤ 53160
  · exact ⟨53089, by norm_num, by omega, by omega⟩
  by_cases h10 : n ≤ 53232
  · exact ⟨53161, by norm_num, by omega, by omega⟩
  by_cases h11 : n ≤ 53304
  · exact ⟨53233, by norm_num, by omega, by omega⟩
  by_cases h12 : n ≤ 53370
  · exact ⟨53299, by norm_num, by omega, by omega⟩
  by_cases h13 : n ≤ 53430
  · exact ⟨53359, by norm_num, by omega, by omega⟩
  by_cases h14 : n ≤ 53490
  · exact ⟨53419, by norm_num, by omega, by omega⟩
  by_cases h15 : n ≤ 53550
  · exact ⟨53479, by norm_num, by omega, by omega⟩
  by_cases h16 : n ≤ 53622
  · exact ⟨53551, by norm_num, by omega, by omega⟩
  by_cases h17 : n ≤ 53694
  · exact ⟨53623, by norm_num, by omega, by omega⟩
  by_cases h18 : n ≤ 53764
  · exact ⟨53693, by norm_num, by omega, by omega⟩
  by_cases h19 : n ≤ 53830
  · exact ⟨53759, by norm_num, by omega, by omega⟩
  by_cases h20 : n ≤ 53902
  · exact ⟨53831, by norm_num, by omega, by omega⟩
  by_cases h21 : n ≤ 53970
  · exact ⟨53899, by norm_num, by omega, by omega⟩
  by_cases h22 : n ≤ 54030
  · exact ⟨53959, by norm_num, by omega, by omega⟩
  by_cases h23 : n ≤ 54084
  · exact ⟨54013, by norm_num, by omega, by omega⟩
  by_cases h24 : n ≤ 54154
  · exact ⟨54083, by norm_num, by omega, by omega⟩
  by_cases h25 : n ≤ 54222
  · exact ⟨54151, by norm_num, by omega, by omega⟩
  by_cases h26 : n ≤ 54288
  · exact ⟨54217, by norm_num, by omega, by omega⟩
  by_cases h27 : n ≤ 54358
  · exact ⟨54287, by norm_num, by omega, by omega⟩
  by_cases h28 : n ≤ 54418
  · exact ⟨54347, by norm_num, by omega, by omega⟩
  by_cases h29 : n ≤ 54490
  · exact ⟨54419, by norm_num, by omega, by omega⟩
  by_cases h30 : n ≤ 54540
  · exact ⟨54469, by norm_num, by omega, by omega⟩
  by_cases h31 : n ≤ 54612
  · exact ⟨54541, by norm_num, by omega, by omega⟩
  by_cases h32 : n ≤ 54672
  · exact ⟨54601, by norm_num, by omega, by omega⟩
  by_cases h33 : n ≤ 54744
  · exact ⟨54673, by norm_num, by omega, by omega⟩
  by_cases h34 : n ≤ 54798
  · exact ⟨54727, by norm_num, by omega, by omega⟩
  by_cases h35 : n ≤ 54870
  · exact ⟨54799, by norm_num, by omega, by omega⟩
  by_cases h36 : n ≤ 54940
  · exact ⟨54869, by norm_num, by omega, by omega⟩
  · exact ⟨54941, by norm_num, by omega, by omega⟩

set_option maxHeartbeats 800000 in
