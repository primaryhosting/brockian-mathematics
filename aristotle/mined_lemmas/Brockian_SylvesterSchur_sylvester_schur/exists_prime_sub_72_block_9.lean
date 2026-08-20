import Mathlib
import SylvesterSchurCore
namespace Brockian.SylvesterSchur
/-- Sylvester–Schur: for n > k ≥ 1, some element of {n+1,…,n+k} has a prime factor > k. -/

lemma exists_prime_sub_72_block_9 (n : ℕ) (hlo : 22501 ≤ n) (hhi : n ≤ 25000) :
    ∃ p : ℕ, p.Prime ∧ n - 72 < p ∧ p ≤ n := by
  by_cases h0 : n ≤ 22572
  · exact ⟨22501, by norm_num, by omega, by omega⟩
  by_cases h1 : n ≤ 22644
  · exact ⟨22573, by norm_num, by omega, by omega⟩
  by_cases h2 : n ≤ 22714
  · exact ⟨22643, by norm_num, by omega, by omega⟩
  by_cases h3 : n ≤ 22780
  · exact ⟨22709, by norm_num, by omega, by omega⟩
  by_cases h4 : n ≤ 22848
  · exact ⟨22777, by norm_num, by omega, by omega⟩
  by_cases h5 : n ≤ 22888
  · exact ⟨22817, by norm_num, by omega, by omega⟩
  by_cases h6 : n ≤ 22948
  · exact ⟨22877, by norm_num, by omega, by omega⟩
  by_cases h7 : n ≤ 23014
  · exact ⟨22943, by norm_num, by omega, by omega⟩
  by_cases h8 : n ≤ 23082
  · exact ⟨23011, by norm_num, by omega, by omega⟩
  by_cases h9 : n ≤ 23152
  · exact ⟨23081, by norm_num, by omega, by omega⟩
  by_cases h10 : n ≤ 23214
  · exact ⟨23143, by norm_num, by omega, by omega⟩
  by_cases h11 : n ≤ 23280
  · exact ⟨23209, by norm_num, by omega, by omega⟩
  by_cases h12 : n ≤ 23350
  · exact ⟨23279, by norm_num, by omega, by omega⟩
  by_cases h13 : n ≤ 23410
  · exact ⟨23339, by norm_num, by omega, by omega⟩
  by_cases h14 : n ≤ 23470
  · exact ⟨23399, by norm_num, by omega, by omega⟩
  by_cases h15 : n ≤ 23530
  · exact ⟨23459, by norm_num, by omega, by omega⟩
  by_cases h16 : n ≤ 23602
  · exact ⟨23531, by norm_num, by omega, by omega⟩
  by_cases h17 : n ≤ 23674
  · exact ⟨23603, by norm_num, by omega, by omega⟩
  by_cases h18 : n ≤ 23742
  · exact ⟨23671, by norm_num, by omega, by omega⟩
  by_cases h19 : n ≤ 23814
  · exact ⟨23743, by norm_num, by omega, by omega⟩
  by_cases h20 : n ≤ 23884
  · exact ⟨23813, by norm_num, by omega, by omega⟩
  by_cases h21 : n ≤ 23950
  · exact ⟨23879, by norm_num, by omega, by omega⟩
  by_cases h22 : n ≤ 24000
  · exact ⟨23929, by norm_num, by omega, by omega⟩
  by_cases h23 : n ≤ 24072
  · exact ⟨24001, by norm_num, by omega, by omega⟩
  by_cases h24 : n ≤ 24142
  · exact ⟨24071, by norm_num, by omega, by omega⟩
  by_cases h25 : n ≤ 24208
  · exact ⟨24137, by norm_num, by omega, by omega⟩
  by_cases h26 : n ≤ 24274
  · exact ⟨24203, by norm_num, by omega, by omega⟩
  by_cases h27 : n ≤ 24322
  · exact ⟨24251, by norm_num, by omega, by omega⟩
  by_cases h28 : n ≤ 24388
  · exact ⟨24317, by norm_num, by omega, by omega⟩
  by_cases h29 : n ≤ 24450
  · exact ⟨24379, by norm_num, by omega, by omega⟩
  by_cases h30 : n ≤ 24514
  · exact ⟨24443, by norm_num, by omega, by omega⟩
  by_cases h31 : n ≤ 24580
  · exact ⟨24509, by norm_num, by omega, by omega⟩
  by_cases h32 : n ≤ 24642
  · exact ⟨24571, by norm_num, by omega, by omega⟩
  by_cases h33 : n ≤ 24702
  · exact ⟨24631, by norm_num, by omega, by omega⟩
  by_cases h34 : n ≤ 24768
  · exact ⟨24697, by norm_num, by omega, by omega⟩
  by_cases h35 : n ≤ 24838
  · exact ⟨24767, by norm_num, by omega, by omega⟩
  by_cases h36 : n ≤ 24892
  · exact ⟨24821, by norm_num, by omega, by omega⟩
  by_cases h37 : n ≤ 24960
  · exact ⟨24889, by norm_num, by omega, by omega⟩
  · exact ⟨24953, by norm_num, by omega, by omega⟩

set_option maxHeartbeats 800000 in
