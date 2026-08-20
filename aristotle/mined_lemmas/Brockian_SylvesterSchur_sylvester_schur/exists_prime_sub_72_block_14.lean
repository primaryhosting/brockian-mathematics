import Mathlib
import SylvesterSchurCore
namespace Brockian.SylvesterSchur
/-- Sylvester–Schur: for n > k ≥ 1, some element of {n+1,…,n+k} has a prime factor > k. -/

lemma exists_prime_sub_72_block_14 (n : ℕ) (hlo : 35001 ≤ n) (hhi : n ≤ 37500) :
    ∃ p : ℕ, p.Prime ∧ n - 72 < p ∧ p ≤ n := by
  by_cases h0 : n ≤ 35052
  · exact ⟨34981, by norm_num, by omega, by omega⟩
  by_cases h1 : n ≤ 35124
  · exact ⟨35053, by norm_num, by omega, by omega⟩
  by_cases h2 : n ≤ 35188
  · exact ⟨35117, by norm_num, by omega, by omega⟩
  by_cases h3 : n ≤ 35242
  · exact ⟨35171, by norm_num, by omega, by omega⟩
  by_cases h4 : n ≤ 35298
  · exact ⟨35227, by norm_num, by omega, by omega⟩
  by_cases h5 : n ≤ 35362
  · exact ⟨35291, by norm_num, by omega, by omega⟩
  by_cases h6 : n ≤ 35434
  · exact ⟨35363, by norm_num, by omega, by omega⟩
  by_cases h7 : n ≤ 35494
  · exact ⟨35423, by norm_num, by omega, by omega⟩
  by_cases h8 : n ≤ 35562
  · exact ⟨35491, by norm_num, by omega, by omega⟩
  by_cases h9 : n ≤ 35614
  · exact ⟨35543, by norm_num, by omega, by omega⟩
  by_cases h10 : n ≤ 35674
  · exact ⟨35603, by norm_num, by omega, by omega⟩
  by_cases h11 : n ≤ 35742
  · exact ⟨35671, by norm_num, by omega, by omega⟩
  by_cases h12 : n ≤ 35802
  · exact ⟨35731, by norm_num, by omega, by omega⟩
  by_cases h13 : n ≤ 35874
  · exact ⟨35803, by norm_num, by omega, by omega⟩
  by_cases h14 : n ≤ 35940
  · exact ⟨35869, by norm_num, by omega, by omega⟩
  by_cases h15 : n ≤ 36004
  · exact ⟨35933, by norm_num, by omega, by omega⟩
  by_cases h16 : n ≤ 36070
  · exact ⟨35999, by norm_num, by omega, by omega⟩
  by_cases h17 : n ≤ 36138
  · exact ⟨36067, by norm_num, by omega, by omega⟩
  by_cases h18 : n ≤ 36208
  · exact ⟨36137, by norm_num, by omega, by omega⟩
  by_cases h19 : n ≤ 36280
  · exact ⟨36209, by norm_num, by omega, by omega⟩
  by_cases h20 : n ≤ 36348
  · exact ⟨36277, by norm_num, by omega, by omega⟩
  by_cases h21 : n ≤ 36414
  · exact ⟨36343, by norm_num, by omega, by omega⟩
  by_cases h22 : n ≤ 36460
  · exact ⟨36389, by norm_num, by omega, by omega⟩
  by_cases h23 : n ≤ 36528
  · exact ⟨36457, by norm_num, by omega, by omega⟩
  by_cases h24 : n ≤ 36600
  · exact ⟨36529, by norm_num, by omega, by omega⟩
  by_cases h25 : n ≤ 36670
  · exact ⟨36599, by norm_num, by omega, by omega⟩
  by_cases h26 : n ≤ 36742
  · exact ⟨36671, by norm_num, by omega, by omega⟩
  by_cases h27 : n ≤ 36810
  · exact ⟨36739, by norm_num, by omega, by omega⟩
  by_cases h28 : n ≤ 36880
  · exact ⟨36809, by norm_num, by omega, by omega⟩
  by_cases h29 : n ≤ 36948
  · exact ⟨36877, by norm_num, by omega, by omega⟩
  by_cases h30 : n ≤ 37018
  · exact ⟨36947, by norm_num, by omega, by omega⟩
  by_cases h31 : n ≤ 37090
  · exact ⟨37019, by norm_num, by omega, by omega⟩
  by_cases h32 : n ≤ 37158
  · exact ⟨37087, by norm_num, by omega, by omega⟩
  by_cases h33 : n ≤ 37230
  · exact ⟨37159, by norm_num, by omega, by omega⟩
  by_cases h34 : n ≤ 37294
  · exact ⟨37223, by norm_num, by omega, by omega⟩
  by_cases h35 : n ≤ 37348
  · exact ⟨37277, by norm_num, by omega, by omega⟩
  by_cases h36 : n ≤ 37410
  · exact ⟨37339, by norm_num, by omega, by omega⟩
  by_cases h37 : n ≤ 37480
  · exact ⟨37409, by norm_num, by omega, by omega⟩
  · exact ⟨37463, by norm_num, by omega, by omega⟩

set_option maxHeartbeats 800000 in
