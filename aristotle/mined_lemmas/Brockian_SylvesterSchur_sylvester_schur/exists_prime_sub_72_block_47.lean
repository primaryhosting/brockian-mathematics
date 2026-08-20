import Mathlib
import SylvesterSchurCore
namespace Brockian.SylvesterSchur
/-- Sylvester–Schur: for n > k ≥ 1, some element of {n+1,…,n+k} has a prime factor > k. -/

lemma exists_prime_sub_72_block_47 (n : ℕ) (hlo : 117501 ≤ n) (hhi : n ≤ 120000) :
    ∃ p : ℕ, p.Prime ∧ n - 72 < p ∧ p ≤ n := by
  by_cases h0 : n ≤ 117570
  · exact ⟨117499, by norm_num, by omega, by omega⟩
  by_cases h1 : n ≤ 117642
  · exact ⟨117571, by norm_num, by omega, by omega⟩
  by_cases h2 : n ≤ 117714
  · exact ⟨117643, by norm_num, by omega, by omega⟩
  by_cases h3 : n ≤ 117780
  · exact ⟨117709, by norm_num, by omega, by omega⟩
  by_cases h4 : n ≤ 117850
  · exact ⟨117779, by norm_num, by omega, by omega⟩
  by_cases h5 : n ≤ 117922
  · exact ⟨117851, by norm_num, by omega, by omega⟩
  by_cases h6 : n ≤ 117988
  · exact ⟨117917, by norm_num, by omega, by omega⟩
  by_cases h7 : n ≤ 118060
  · exact ⟨117989, by norm_num, by omega, by omega⟩
  by_cases h8 : n ≤ 118132
  · exact ⟨118061, by norm_num, by omega, by omega⟩
  by_cases h9 : n ≤ 118198
  · exact ⟨118127, by norm_num, by omega, by omega⟩
  by_cases h10 : n ≤ 118260
  · exact ⟨118189, by norm_num, by omega, by omega⟩
  by_cases h11 : n ≤ 118330
  · exact ⟨118259, by norm_num, by omega, by omega⟩
  by_cases h12 : n ≤ 118368
  · exact ⟨118297, by norm_num, by omega, by omega⟩
  by_cases h13 : n ≤ 118440
  · exact ⟨118369, by norm_num, by omega, by omega⟩
  by_cases h14 : n ≤ 118500
  · exact ⟨118429, by norm_num, by omega, by omega⟩
  by_cases h15 : n ≤ 118564
  · exact ⟨118493, by norm_num, by omega, by omega⟩
  by_cases h16 : n ≤ 118620
  · exact ⟨118549, by norm_num, by omega, by omega⟩
  by_cases h17 : n ≤ 118692
  · exact ⟨118621, by norm_num, by omega, by omega⟩
  by_cases h18 : n ≤ 118762
  · exact ⟨118691, by norm_num, by omega, by omega⟩
  by_cases h19 : n ≤ 118828
  · exact ⟨118757, by norm_num, by omega, by omega⟩
  by_cases h20 : n ≤ 118890
  · exact ⟨118819, by norm_num, by omega, by omega⟩
  by_cases h21 : n ≤ 118962
  · exact ⟨118891, by norm_num, by omega, by omega⟩
  by_cases h22 : n ≤ 119002
  · exact ⟨118931, by norm_num, by omega, by omega⟩
  by_cases h23 : n ≤ 119044
  · exact ⟨118973, by norm_num, by omega, by omega⟩
  by_cases h24 : n ≤ 119110
  · exact ⟨119039, by norm_num, by omega, by omega⟩
  by_cases h25 : n ≤ 119178
  · exact ⟨119107, by norm_num, by omega, by omega⟩
  by_cases h26 : n ≤ 119250
  · exact ⟨119179, by norm_num, by omega, by omega⟩
  by_cases h27 : n ≤ 119314
  · exact ⟨119243, by norm_num, by omega, by omega⟩
  by_cases h28 : n ≤ 119382
  · exact ⟨119311, by norm_num, by omega, by omega⟩
  by_cases h29 : n ≤ 119434
  · exact ⟨119363, by norm_num, by omega, by omega⟩
  by_cases h30 : n ≤ 119500
  · exact ⟨119429, by norm_num, by omega, by omega⟩
  by_cases h31 : n ≤ 119560
  · exact ⟨119489, by norm_num, by omega, by omega⟩
  by_cases h32 : n ≤ 119628
  · exact ⟨119557, by norm_num, by omega, by omega⟩
  by_cases h33 : n ≤ 119698
  · exact ⟨119627, by norm_num, by omega, by omega⟩
  by_cases h34 : n ≤ 119770
  · exact ⟨119699, by norm_num, by omega, by omega⟩
  by_cases h35 : n ≤ 119842
  · exact ⟨119771, by norm_num, by omega, by omega⟩
  by_cases h36 : n ≤ 119910
  · exact ⟨119839, by norm_num, by omega, by omega⟩
  by_cases h37 : n ≤ 119962
  · exact ⟨119891, by norm_num, by omega, by omega⟩
  · exact ⟨119963, by norm_num, by omega, by omega⟩

set_option maxHeartbeats 800000 in
