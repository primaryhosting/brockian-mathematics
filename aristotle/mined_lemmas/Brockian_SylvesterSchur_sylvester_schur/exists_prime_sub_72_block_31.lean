import Mathlib
import SylvesterSchurCore
namespace Brockian.SylvesterSchur
/-- Sylvester–Schur: for n > k ≥ 1, some element of {n+1,…,n+k} has a prime factor > k. -/

lemma exists_prime_sub_72_block_31 (n : ℕ) (hlo : 77501 ≤ n) (hhi : n ≤ 80000) :
    ∃ p : ℕ, p.Prime ∧ n - 72 < p ∧ p ≤ n := by
  by_cases h0 : n ≤ 77562
  · exact ⟨77491, by norm_num, by omega, by omega⟩
  by_cases h1 : n ≤ 77634
  · exact ⟨77563, by norm_num, by omega, by omega⟩
  by_cases h2 : n ≤ 77692
  · exact ⟨77621, by norm_num, by omega, by omega⟩
  by_cases h3 : n ≤ 77760
  · exact ⟨77689, by norm_num, by omega, by omega⟩
  by_cases h4 : n ≤ 77832
  · exact ⟨77761, by norm_num, by omega, by omega⟩
  by_cases h5 : n ≤ 77884
  · exact ⟨77813, by norm_num, by omega, by omega⟩
  by_cases h6 : n ≤ 77938
  · exact ⟨77867, by norm_num, by omega, by omega⟩
  by_cases h7 : n ≤ 78004
  · exact ⟨77933, by norm_num, by omega, by omega⟩
  by_cases h8 : n ≤ 78070
  · exact ⟨77999, by norm_num, by omega, by omega⟩
  by_cases h9 : n ≤ 78130
  · exact ⟨78059, by norm_num, by omega, by omega⟩
  by_cases h10 : n ≤ 78192
  · exact ⟨78121, by norm_num, by omega, by omega⟩
  by_cases h11 : n ≤ 78264
  · exact ⟨78193, by norm_num, by omega, by omega⟩
  by_cases h12 : n ≤ 78330
  · exact ⟨78259, by norm_num, by omega, by omega⟩
  by_cases h13 : n ≤ 78388
  · exact ⟨78317, by norm_num, by omega, by omega⟩
  by_cases h14 : n ≤ 78438
  · exact ⟨78367, by norm_num, by omega, by omega⟩
  by_cases h15 : n ≤ 78510
  · exact ⟨78439, by norm_num, by omega, by omega⟩
  by_cases h16 : n ≤ 78582
  · exact ⟨78511, by norm_num, by omega, by omega⟩
  by_cases h17 : n ≤ 78654
  · exact ⟨78583, by norm_num, by omega, by omega⟩
  by_cases h18 : n ≤ 78724
  · exact ⟨78653, by norm_num, by omega, by omega⟩
  by_cases h19 : n ≤ 78792
  · exact ⟨78721, by norm_num, by omega, by omega⟩
  by_cases h20 : n ≤ 78862
  · exact ⟨78791, by norm_num, by omega, by omega⟩
  by_cases h21 : n ≤ 78928
  · exact ⟨78857, by norm_num, by omega, by omega⟩
  by_cases h22 : n ≤ 79000
  · exact ⟨78929, by norm_num, by omega, by omega⟩
  by_cases h23 : n ≤ 79060
  · exact ⟨78989, by norm_num, by omega, by omega⟩
  by_cases h24 : n ≤ 79114
  · exact ⟨79043, by norm_num, by omega, by omega⟩
  by_cases h25 : n ≤ 79182
  · exact ⟨79111, by norm_num, by omega, by omega⟩
  by_cases h26 : n ≤ 79252
  · exact ⟨79181, by norm_num, by omega, by omega⟩
  by_cases h27 : n ≤ 79312
  · exact ⟨79241, by norm_num, by omega, by omega⟩
  by_cases h28 : n ≤ 79380
  · exact ⟨79309, by norm_num, by omega, by omega⟩
  by_cases h29 : n ≤ 79450
  · exact ⟨79379, by norm_num, by omega, by omega⟩
  by_cases h30 : n ≤ 79522
  · exact ⟨79451, by norm_num, by omega, by omega⟩
  by_cases h31 : n ≤ 79564
  · exact ⟨79493, by norm_num, by omega, by omega⟩
  by_cases h32 : n ≤ 79632
  · exact ⟨79561, by norm_num, by omega, by omega⟩
  by_cases h33 : n ≤ 79704
  · exact ⟨79633, by norm_num, by omega, by omega⟩
  by_cases h34 : n ≤ 79770
  · exact ⟨79699, by norm_num, by omega, by omega⟩
  by_cases h35 : n ≤ 79840
  · exact ⟨79769, by norm_num, by omega, by omega⟩
  by_cases h36 : n ≤ 79912
  · exact ⟨79841, by norm_num, by omega, by omega⟩
  by_cases h37 : n ≤ 79978
  · exact ⟨79907, by norm_num, by omega, by omega⟩
  · exact ⟨79979, by norm_num, by omega, by omega⟩

set_option maxHeartbeats 800000 in
