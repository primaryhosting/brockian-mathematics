import Mathlib
import SylvesterSchurCore
namespace Brockian.SylvesterSchur
/-- Sylvester–Schur: for n > k ≥ 1, some element of {n+1,…,n+k} has a prime factor > k. -/

lemma exists_prime_sub_72_block_20 (n : ℕ) (hlo : 50001 ≤ n) (hhi : n ≤ 52500) :
    ∃ p : ℕ, p.Prime ∧ n - 72 < p ∧ p ≤ n := by
  by_cases h0 : n ≤ 50070
  · exact ⟨49999, by norm_num, by omega, by omega⟩
  by_cases h1 : n ≤ 50140
  · exact ⟨50069, by norm_num, by omega, by omega⟩
  by_cases h2 : n ≤ 50202
  · exact ⟨50131, by norm_num, by omega, by omega⟩
  by_cases h3 : n ≤ 50248
  · exact ⟨50177, by norm_num, by omega, by omega⟩
  by_cases h4 : n ≤ 50302
  · exact ⟨50231, by norm_num, by omega, by omega⟩
  by_cases h5 : n ≤ 50362
  · exact ⟨50291, by norm_num, by omega, by omega⟩
  by_cases h6 : n ≤ 50434
  · exact ⟨50363, by norm_num, by omega, by omega⟩
  by_cases h7 : n ≤ 50494
  · exact ⟨50423, by norm_num, by omega, by omega⟩
  by_cases h8 : n ≤ 50532
  · exact ⟨50461, by norm_num, by omega, by omega⟩
  by_cases h9 : n ≤ 50598
  · exact ⟨50527, by norm_num, by omega, by omega⟩
  by_cases h10 : n ≤ 50670
  · exact ⟨50599, by norm_num, by omega, by omega⟩
  by_cases h11 : n ≤ 50742
  · exact ⟨50671, by norm_num, by omega, by omega⟩
  by_cases h12 : n ≤ 50812
  · exact ⟨50741, by norm_num, by omega, by omega⟩
  by_cases h13 : n ≤ 50860
  · exact ⟨50789, by norm_num, by omega, by omega⟩
  by_cases h14 : n ≤ 50928
  · exact ⟨50857, by norm_num, by omega, by omega⟩
  by_cases h15 : n ≤ 51000
  · exact ⟨50929, by norm_num, by omega, by omega⟩
  by_cases h16 : n ≤ 51072
  · exact ⟨51001, by norm_num, by omega, by omega⟩
  by_cases h17 : n ≤ 51142
  · exact ⟨51071, by norm_num, by omega, by omega⟩
  by_cases h18 : n ≤ 51208
  · exact ⟨51137, by norm_num, by omega, by omega⟩
  by_cases h19 : n ≤ 51274
  · exact ⟨51203, by norm_num, by omega, by omega⟩
  by_cases h20 : n ≤ 51334
  · exact ⟨51263, by norm_num, by omega, by omega⟩
  by_cases h21 : n ≤ 51400
  · exact ⟨51329, by norm_num, by omega, by omega⟩
  by_cases h22 : n ≤ 51454
  · exact ⟨51383, by norm_num, by omega, by omega⟩
  by_cases h23 : n ≤ 51520
  · exact ⟨51449, by norm_num, by omega, by omega⟩
  by_cases h24 : n ≤ 51592
  · exact ⟨51521, by norm_num, by omega, by omega⟩
  by_cases h25 : n ≤ 51664
  · exact ⟨51593, by norm_num, by omega, by omega⟩
  by_cases h26 : n ≤ 51730
  · exact ⟨51659, by norm_num, by omega, by omega⟩
  by_cases h27 : n ≤ 51792
  · exact ⟨51721, by norm_num, by omega, by omega⟩
  by_cases h28 : n ≤ 51858
  · exact ⟨51787, by norm_num, by omega, by omega⟩
  by_cases h29 : n ≤ 51930
  · exact ⟨51859, by norm_num, by omega, by omega⟩
  by_cases h30 : n ≤ 52000
  · exact ⟨51929, by norm_num, by omega, by omega⟩
  by_cases h31 : n ≤ 52062
  · exact ⟨51991, by norm_num, by omega, by omega⟩
  by_cases h32 : n ≤ 52128
  · exact ⟨52057, by norm_num, by omega, by omega⟩
  by_cases h33 : n ≤ 52198
  · exact ⟨52127, by norm_num, by omega, by omega⟩
  by_cases h34 : n ≤ 52260
  · exact ⟨52189, by norm_num, by omega, by omega⟩
  by_cases h35 : n ≤ 52330
  · exact ⟨52259, by norm_num, by omega, by omega⟩
  by_cases h36 : n ≤ 52392
  · exact ⟨52321, by norm_num, by omega, by omega⟩
  by_cases h37 : n ≤ 52462
  · exact ⟨52391, by norm_num, by omega, by omega⟩
  · exact ⟨52457, by norm_num, by omega, by omega⟩

set_option maxHeartbeats 800000 in
