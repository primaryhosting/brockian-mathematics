import Mathlib
import SylvesterSchurCore
namespace Brockian.SylvesterSchur
/-- Sylvester–Schur: for n > k ≥ 1, some element of {n+1,…,n+k} has a prime factor > k. -/

lemma exists_prime_sub_72_block_1 (n : ℕ) (hlo : 2501 ≤ n) (hhi : n ≤ 5000) :
    ∃ p : ℕ, p.Prime ∧ n - 72 < p ∧ p ≤ n := by
  by_cases h0 : n ≤ 2548
  · exact ⟨2477, by norm_num, by omega, by omega⟩
  by_cases h1 : n ≤ 2620
  · exact ⟨2549, by norm_num, by omega, by omega⟩
  by_cases h2 : n ≤ 2692
  · exact ⟨2621, by norm_num, by omega, by omega⟩
  by_cases h3 : n ≤ 2764
  · exact ⟨2693, by norm_num, by omega, by omega⟩
  by_cases h4 : n ≤ 2824
  · exact ⟨2753, by norm_num, by omega, by omega⟩
  by_cases h5 : n ≤ 2890
  · exact ⟨2819, by norm_num, by omega, by omega⟩
  by_cases h6 : n ≤ 2958
  · exact ⟨2887, by norm_num, by omega, by omega⟩
  by_cases h7 : n ≤ 3028
  · exact ⟨2957, by norm_num, by omega, by omega⟩
  by_cases h8 : n ≤ 3094
  · exact ⟨3023, by norm_num, by omega, by omega⟩
  by_cases h9 : n ≤ 3160
  · exact ⟨3089, by norm_num, by omega, by omega⟩
  by_cases h10 : n ≤ 3208
  · exact ⟨3137, by norm_num, by omega, by omega⟩
  by_cases h11 : n ≤ 3280
  · exact ⟨3209, by norm_num, by omega, by omega⟩
  by_cases h12 : n ≤ 3342
  · exact ⟨3271, by norm_num, by omega, by omega⟩
  by_cases h13 : n ≤ 3414
  · exact ⟨3343, by norm_num, by omega, by omega⟩
  by_cases h14 : n ≤ 3484
  · exact ⟨3413, by norm_num, by omega, by omega⟩
  by_cases h15 : n ≤ 3540
  · exact ⟨3469, by norm_num, by omega, by omega⟩
  by_cases h16 : n ≤ 3612
  · exact ⟨3541, by norm_num, by omega, by omega⟩
  by_cases h17 : n ≤ 3684
  · exact ⟨3613, by norm_num, by omega, by omega⟩
  by_cases h18 : n ≤ 3748
  · exact ⟨3677, by norm_num, by omega, by omega⟩
  by_cases h19 : n ≤ 3810
  · exact ⟨3739, by norm_num, by omega, by omega⟩
  by_cases h20 : n ≤ 3874
  · exact ⟨3803, by norm_num, by omega, by omega⟩
  by_cases h21 : n ≤ 3934
  · exact ⟨3863, by norm_num, by omega, by omega⟩
  by_cases h22 : n ≤ 4002
  · exact ⟨3931, by norm_num, by omega, by omega⟩
  by_cases h23 : n ≤ 4074
  · exact ⟨4003, by norm_num, by omega, by omega⟩
  by_cases h24 : n ≤ 4144
  · exact ⟨4073, by norm_num, by omega, by omega⟩
  by_cases h25 : n ≤ 4210
  · exact ⟨4139, by norm_num, by omega, by omega⟩
  by_cases h26 : n ≤ 4282
  · exact ⟨4211, by norm_num, by omega, by omega⟩
  by_cases h27 : n ≤ 4354
  · exact ⟨4283, by norm_num, by omega, by omega⟩
  by_cases h28 : n ≤ 4420
  · exact ⟨4349, by norm_num, by omega, by omega⟩
  by_cases h29 : n ≤ 4492
  · exact ⟨4421, by norm_num, by omega, by omega⟩
  by_cases h30 : n ≤ 4564
  · exact ⟨4493, by norm_num, by omega, by omega⟩
  by_cases h31 : n ≤ 4632
  · exact ⟨4561, by norm_num, by omega, by omega⟩
  by_cases h32 : n ≤ 4692
  · exact ⟨4621, by norm_num, by omega, by omega⟩
  by_cases h33 : n ≤ 4762
  · exact ⟨4691, by norm_num, by omega, by omega⟩
  by_cases h34 : n ≤ 4830
  · exact ⟨4759, by norm_num, by omega, by omega⟩
  by_cases h35 : n ≤ 4902
  · exact ⟨4831, by norm_num, by omega, by omega⟩
  by_cases h36 : n ≤ 4974
  · exact ⟨4903, by norm_num, by omega, by omega⟩
  · exact ⟨4973, by norm_num, by omega, by omega⟩

set_option maxHeartbeats 800000 in
