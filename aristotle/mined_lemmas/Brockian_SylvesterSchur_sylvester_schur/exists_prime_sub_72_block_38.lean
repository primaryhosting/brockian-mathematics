import Mathlib
import SylvesterSchurCore
namespace Brockian.SylvesterSchur
/-- Sylvester–Schur: for n > k ≥ 1, some element of {n+1,…,n+k} has a prime factor > k. -/

lemma exists_prime_sub_72_block_38 (n : ℕ) (hlo : 95001 ≤ n) (hhi : n ≤ 97500) :
    ∃ p : ℕ, p.Prime ∧ n - 72 < p ∧ p ≤ n := by
  by_cases h0 : n ≤ 95070
  · exact ⟨94999, by norm_num, by omega, by omega⟩
  by_cases h1 : n ≤ 95142
  · exact ⟨95071, by norm_num, by omega, by omega⟩
  by_cases h2 : n ≤ 95214
  · exact ⟨95143, by norm_num, by omega, by omega⟩
  by_cases h3 : n ≤ 95284
  · exact ⟨95213, by norm_num, by omega, by omega⟩
  by_cases h4 : n ≤ 95350
  · exact ⟨95279, by norm_num, by omega, by omega⟩
  by_cases h5 : n ≤ 95410
  · exact ⟨95339, by norm_num, by omega, by omega⟩
  by_cases h6 : n ≤ 95472
  · exact ⟨95401, by norm_num, by omega, by omega⟩
  by_cases h7 : n ≤ 95542
  · exact ⟨95471, by norm_num, by omega, by omega⟩
  by_cases h8 : n ≤ 95610
  · exact ⟨95539, by norm_num, by omega, by omega⟩
  by_cases h9 : n ≤ 95674
  · exact ⟨95603, by norm_num, by omega, by omega⟩
  by_cases h10 : n ≤ 95722
  · exact ⟨95651, by norm_num, by omega, by omega⟩
  by_cases h11 : n ≤ 95794
  · exact ⟨95723, by norm_num, by omega, by omega⟩
  by_cases h12 : n ≤ 95862
  · exact ⟨95791, by norm_num, by omega, by omega⟩
  by_cases h13 : n ≤ 95928
  · exact ⟨95857, by norm_num, by omega, by omega⟩
  by_cases h14 : n ≤ 96000
  · exact ⟨95929, by norm_num, by omega, by omega⟩
  by_cases h15 : n ≤ 96072
  · exact ⟨96001, by norm_num, by omega, by omega⟩
  by_cases h16 : n ≤ 96130
  · exact ⟨96059, by norm_num, by omega, by omega⟩
  by_cases h17 : n ≤ 96168
  · exact ⟨96097, by norm_num, by omega, by omega⟩
  by_cases h18 : n ≤ 96238
  · exact ⟨96167, by norm_num, by omega, by omega⟩
  by_cases h19 : n ≤ 96304
  · exact ⟨96233, by norm_num, by omega, by omega⟩
  by_cases h20 : n ≤ 96364
  · exact ⟨96293, by norm_num, by omega, by omega⟩
  by_cases h21 : n ≤ 96424
  · exact ⟨96353, by norm_num, by omega, by omega⟩
  by_cases h22 : n ≤ 96490
  · exact ⟨96419, by norm_num, by omega, by omega⟩
  by_cases h23 : n ≤ 96558
  · exact ⟨96487, by norm_num, by omega, by omega⟩
  by_cases h24 : n ≤ 96628
  · exact ⟨96557, by norm_num, by omega, by omega⟩
  by_cases h25 : n ≤ 96672
  · exact ⟨96601, by norm_num, by omega, by omega⟩
  by_cases h26 : n ≤ 96742
  · exact ⟨96671, by norm_num, by omega, by omega⟩
  by_cases h27 : n ≤ 96810
  · exact ⟨96739, by norm_num, by omega, by omega⟩
  by_cases h28 : n ≤ 96870
  · exact ⟨96799, by norm_num, by omega, by omega⟩
  by_cases h29 : n ≤ 96928
  · exact ⟨96857, by norm_num, by omega, by omega⟩
  by_cases h30 : n ≤ 96982
  · exact ⟨96911, by norm_num, by omega, by omega⟩
  by_cases h31 : n ≤ 97050
  · exact ⟨96979, by norm_num, by omega, by omega⟩
  by_cases h32 : n ≤ 97110
  · exact ⟨97039, by norm_num, by omega, by omega⟩
  by_cases h33 : n ≤ 97174
  · exact ⟨97103, by norm_num, by omega, by omega⟩
  by_cases h34 : n ≤ 97242
  · exact ⟨97171, by norm_num, by omega, by omega⟩
  by_cases h35 : n ≤ 97312
  · exact ⟨97241, by norm_num, by omega, by omega⟩
  by_cases h36 : n ≤ 97374
  · exact ⟨97303, by norm_num, by omega, by omega⟩
  by_cases h37 : n ≤ 97444
  · exact ⟨97373, by norm_num, by omega, by omega⟩
  · exact ⟨97441, by norm_num, by omega, by omega⟩

set_option maxHeartbeats 800000 in
