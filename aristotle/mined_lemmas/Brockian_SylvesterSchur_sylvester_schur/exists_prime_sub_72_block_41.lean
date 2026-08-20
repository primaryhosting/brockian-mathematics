import Mathlib
import SylvesterSchurCore
namespace Brockian.SylvesterSchur
/-- Sylvester–Schur: for n > k ≥ 1, some element of {n+1,…,n+k} has a prime factor > k. -/

lemma exists_prime_sub_72_block_41 (n : ℕ) (hlo : 102501 ≤ n) (hhi : n ≤ 105000) :
    ∃ p : ℕ, p.Prime ∧ n - 72 < p ∧ p ≤ n := by
  by_cases h0 : n ≤ 102570
  · exact ⟨102499, by norm_num, by omega, by omega⟩
  by_cases h1 : n ≤ 102634
  · exact ⟨102563, by norm_num, by omega, by omega⟩
  by_cases h2 : n ≤ 102682
  · exact ⟨102611, by norm_num, by omega, by omega⟩
  by_cases h3 : n ≤ 102750
  · exact ⟨102679, by norm_num, by omega, by omega⟩
  by_cases h4 : n ≤ 102772
  · exact ⟨102701, by norm_num, by omega, by omega⟩
  by_cases h5 : n ≤ 102840
  · exact ⟨102769, by norm_num, by omega, by omega⟩
  by_cases h6 : n ≤ 102912
  · exact ⟨102841, by norm_num, by omega, by omega⟩
  by_cases h7 : n ≤ 102984
  · exact ⟨102913, by norm_num, by omega, by omega⟩
  by_cases h8 : n ≤ 103054
  · exact ⟨102983, by norm_num, by omega, by omega⟩
  by_cases h9 : n ≤ 103120
  · exact ⟨103049, by norm_num, by omega, by omega⟩
  by_cases h10 : n ≤ 103170
  · exact ⟨103099, by norm_num, by omega, by omega⟩
  by_cases h11 : n ≤ 103242
  · exact ⟨103171, by norm_num, by omega, by omega⟩
  by_cases h12 : n ≤ 103308
  · exact ⟨103237, by norm_num, by omega, by omega⟩
  by_cases h13 : n ≤ 103378
  · exact ⟨103307, by norm_num, by omega, by omega⟩
  by_cases h14 : n ≤ 103428
  · exact ⟨103357, by norm_num, by omega, by omega⟩
  by_cases h15 : n ≤ 103494
  · exact ⟨103423, by norm_num, by omega, by omega⟩
  by_cases h16 : n ≤ 103554
  · exact ⟨103483, by norm_num, by omega, by omega⟩
  by_cases h17 : n ≤ 103624
  · exact ⟨103553, by norm_num, by omega, by omega⟩
  by_cases h18 : n ≤ 103690
  · exact ⟨103619, by norm_num, by omega, by omega⟩
  by_cases h19 : n ≤ 103758
  · exact ⟨103687, by norm_num, by omega, by omega⟩
  by_cases h20 : n ≤ 103794
  · exact ⟨103723, by norm_num, by omega, by omega⟩
  by_cases h21 : n ≤ 103858
  · exact ⟨103787, by norm_num, by omega, by omega⟩
  by_cases h22 : n ≤ 103914
  · exact ⟨103843, by norm_num, by omega, by omega⟩
  by_cases h23 : n ≤ 103984
  · exact ⟨103913, by norm_num, by omega, by omega⟩
  by_cases h24 : n ≤ 104052
  · exact ⟨103981, by norm_num, by omega, by omega⟩
  by_cases h25 : n ≤ 104124
  · exact ⟨104053, by norm_num, by omega, by omega⟩
  by_cases h26 : n ≤ 104194
  · exact ⟨104123, by norm_num, by omega, by omega⟩
  by_cases h27 : n ≤ 104254
  · exact ⟨104183, by norm_num, by omega, by omega⟩
  by_cases h28 : n ≤ 104314
  · exact ⟨104243, by norm_num, by omega, by omega⟩
  by_cases h29 : n ≤ 104382
  · exact ⟨104311, by norm_num, by omega, by omega⟩
  by_cases h30 : n ≤ 104454
  · exact ⟨104383, by norm_num, by omega, by omega⟩
  by_cases h31 : n ≤ 104488
  · exact ⟨104417, by norm_num, by omega, by omega⟩
  by_cases h32 : n ≤ 104550
  · exact ⟨104479, by norm_num, by omega, by omega⟩
  by_cases h33 : n ≤ 104622
  · exact ⟨104551, by norm_num, by omega, by omega⟩
  by_cases h34 : n ≤ 104694
  · exact ⟨104623, by norm_num, by omega, by omega⟩
  by_cases h35 : n ≤ 104764
  · exact ⟨104693, by norm_num, by omega, by omega⟩
  by_cases h36 : n ≤ 104832
  · exact ⟨104761, by norm_num, by omega, by omega⟩
  by_cases h37 : n ≤ 104902
  · exact ⟨104831, by norm_num, by omega, by omega⟩
  by_cases h38 : n ≤ 104962
  · exact ⟨104891, by norm_num, by omega, by omega⟩
  · exact ⟨104959, by norm_num, by omega, by omega⟩

set_option maxHeartbeats 800000 in
