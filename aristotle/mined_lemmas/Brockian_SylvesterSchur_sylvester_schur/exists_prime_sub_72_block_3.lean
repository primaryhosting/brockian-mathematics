import Mathlib
import SylvesterSchurCore
namespace Brockian.SylvesterSchur
/-- Sylvester–Schur: for n > k ≥ 1, some element of {n+1,…,n+k} has a prime factor > k. -/

lemma exists_prime_sub_72_block_3 (n : ℕ) (hlo : 7501 ≤ n) (hhi : n ≤ 10000) :
    ∃ p : ℕ, p.Prime ∧ n - 72 < p ∧ p ≤ n := by
  by_cases h0 : n ≤ 7570
  · exact ⟨7499, by norm_num, by omega, by omega⟩
  by_cases h1 : n ≤ 7632
  · exact ⟨7561, by norm_num, by omega, by omega⟩
  by_cases h2 : n ≤ 7692
  · exact ⟨7621, by norm_num, by omega, by omega⟩
  by_cases h3 : n ≤ 7762
  · exact ⟨7691, by norm_num, by omega, by omega⟩
  by_cases h4 : n ≤ 7830
  · exact ⟨7759, by norm_num, by omega, by omega⟩
  by_cases h5 : n ≤ 7900
  · exact ⟨7829, by norm_num, by omega, by omega⟩
  by_cases h6 : n ≤ 7972
  · exact ⟨7901, by norm_num, by omega, by omega⟩
  by_cases h7 : n ≤ 8034
  · exact ⟨7963, by norm_num, by omega, by omega⟩
  by_cases h8 : n ≤ 8088
  · exact ⟨8017, by norm_num, by omega, by omega⟩
  by_cases h9 : n ≤ 8160
  · exact ⟨8089, by norm_num, by omega, by omega⟩
  by_cases h10 : n ≤ 8232
  · exact ⟨8161, by norm_num, by omega, by omega⟩
  by_cases h11 : n ≤ 8304
  · exact ⟨8233, by norm_num, by omega, by omega⟩
  by_cases h12 : n ≤ 8368
  · exact ⟨8297, by norm_num, by omega, by omega⟩
  by_cases h13 : n ≤ 8440
  · exact ⟨8369, by norm_num, by omega, by omega⟩
  by_cases h14 : n ≤ 8502
  · exact ⟨8431, by norm_num, by omega, by omega⟩
  by_cases h15 : n ≤ 8572
  · exact ⟨8501, by norm_num, by omega, by omega⟩
  by_cases h16 : n ≤ 8644
  · exact ⟨8573, by norm_num, by omega, by omega⟩
  by_cases h17 : n ≤ 8712
  · exact ⟨8641, by norm_num, by omega, by omega⟩
  by_cases h18 : n ≤ 8784
  · exact ⟨8713, by norm_num, by omega, by omega⟩
  by_cases h19 : n ≤ 8854
  · exact ⟨8783, by norm_num, by omega, by omega⟩
  by_cases h20 : n ≤ 8920
  · exact ⟨8849, by norm_num, by omega, by omega⟩
  by_cases h21 : n ≤ 8964
  · exact ⟨8893, by norm_num, by omega, by omega⟩
  by_cases h22 : n ≤ 9034
  · exact ⟨8963, by norm_num, by omega, by omega⟩
  by_cases h23 : n ≤ 9100
  · exact ⟨9029, by norm_num, by omega, by omega⟩
  by_cases h24 : n ≤ 9162
  · exact ⟨9091, by norm_num, by omega, by omega⟩
  by_cases h25 : n ≤ 9232
  · exact ⟨9161, by norm_num, by omega, by omega⟩
  by_cases h26 : n ≤ 9298
  · exact ⟨9227, by norm_num, by omega, by omega⟩
  by_cases h27 : n ≤ 9364
  · exact ⟨9293, by norm_num, by omega, by omega⟩
  by_cases h28 : n ≤ 9420
  · exact ⟨9349, by norm_num, by omega, by omega⟩
  by_cases h29 : n ≤ 9492
  · exact ⟨9421, by norm_num, by omega, by omega⟩
  by_cases h30 : n ≤ 9562
  · exact ⟨9491, by norm_num, by omega, by omega⟩
  by_cases h31 : n ≤ 9622
  · exact ⟨9551, by norm_num, by omega, by omega⟩
  by_cases h32 : n ≤ 9694
  · exact ⟨9623, by norm_num, by omega, by omega⟩
  by_cases h33 : n ≤ 9760
  · exact ⟨9689, by norm_num, by omega, by omega⟩
  by_cases h34 : n ≤ 9820
  · exact ⟨9749, by norm_num, by omega, by omega⟩
  by_cases h35 : n ≤ 9888
  · exact ⟨9817, by norm_num, by omega, by omega⟩
  by_cases h36 : n ≤ 9958
  · exact ⟨9887, by norm_num, by omega, by omega⟩
  · exact ⟨9949, by norm_num, by omega, by omega⟩

set_option maxHeartbeats 800000 in
