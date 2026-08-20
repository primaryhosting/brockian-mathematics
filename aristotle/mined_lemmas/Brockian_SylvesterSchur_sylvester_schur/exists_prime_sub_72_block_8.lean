import Mathlib
import SylvesterSchurCore
namespace Brockian.SylvesterSchur
/-- Sylvester–Schur: for n > k ≥ 1, some element of {n+1,…,n+k} has a prime factor > k. -/

lemma exists_prime_sub_72_block_8 (n : ℕ) (hlo : 20001 ≤ n) (hhi : n ≤ 22500) :
    ∃ p : ℕ, p.Prime ∧ n - 72 < p ∧ p ≤ n := by
  by_cases h0 : n ≤ 20068
  · exact ⟨19997, by norm_num, by omega, by omega⟩
  by_cases h1 : n ≤ 20134
  · exact ⟨20063, by norm_num, by omega, by omega⟩
  by_cases h2 : n ≤ 20200
  · exact ⟨20129, by norm_num, by omega, by omega⟩
  by_cases h3 : n ≤ 20272
  · exact ⟨20201, by norm_num, by omega, by omega⟩
  by_cases h4 : n ≤ 20340
  · exact ⟨20269, by norm_num, by omega, by omega⟩
  by_cases h5 : n ≤ 20412
  · exact ⟨20341, by norm_num, by omega, by omega⟩
  by_cases h6 : n ≤ 20482
  · exact ⟨20411, by norm_num, by omega, by omega⟩
  by_cases h7 : n ≤ 20554
  · exact ⟨20483, by norm_num, by omega, by omega⟩
  by_cases h8 : n ≤ 20622
  · exact ⟨20551, by norm_num, by omega, by omega⟩
  by_cases h9 : n ≤ 20682
  · exact ⟨20611, by norm_num, by omega, by omega⟩
  by_cases h10 : n ≤ 20752
  · exact ⟨20681, by norm_num, by omega, by omega⟩
  by_cases h11 : n ≤ 20824
  · exact ⟨20753, by norm_num, by omega, by omega⟩
  by_cases h12 : n ≤ 20880
  · exact ⟨20809, by norm_num, by omega, by omega⟩
  by_cases h13 : n ≤ 20950
  · exact ⟨20879, by norm_num, by omega, by omega⟩
  by_cases h14 : n ≤ 21018
  · exact ⟨20947, by norm_num, by omega, by omega⟩
  by_cases h15 : n ≤ 21090
  · exact ⟨21019, by norm_num, by omega, by omega⟩
  by_cases h16 : n ≤ 21160
  · exact ⟨21089, by norm_num, by omega, by omega⟩
  by_cases h17 : n ≤ 21228
  · exact ⟨21157, by norm_num, by omega, by omega⟩
  by_cases h18 : n ≤ 21298
  · exact ⟨21227, by norm_num, by omega, by omega⟩
  by_cases h19 : n ≤ 21354
  · exact ⟨21283, by norm_num, by omega, by omega⟩
  by_cases h20 : n ≤ 21418
  · exact ⟨21347, by norm_num, by omega, by omega⟩
  by_cases h21 : n ≤ 21490
  · exact ⟨21419, by norm_num, by omega, by omega⟩
  by_cases h22 : n ≤ 21562
  · exact ⟨21491, by norm_num, by omega, by omega⟩
  by_cases h23 : n ≤ 21634
  · exact ⟨21563, by norm_num, by omega, by omega⟩
  by_cases h24 : n ≤ 21688
  · exact ⟨21617, by norm_num, by omega, by omega⟩
  by_cases h25 : n ≤ 21754
  · exact ⟨21683, by norm_num, by omega, by omega⟩
  by_cases h26 : n ≤ 21822
  · exact ⟨21751, by norm_num, by omega, by omega⟩
  by_cases h27 : n ≤ 21892
  · exact ⟨21821, by norm_num, by omega, by omega⟩
  by_cases h28 : n ≤ 21964
  · exact ⟨21893, by norm_num, by omega, by omega⟩
  by_cases h29 : n ≤ 22032
  · exact ⟨21961, by norm_num, by omega, by omega⟩
  by_cases h30 : n ≤ 22102
  · exact ⟨22031, by norm_num, by omega, by omega⟩
  by_cases h31 : n ≤ 22164
  · exact ⟨22093, by norm_num, by omega, by omega⟩
  by_cases h32 : n ≤ 22230
  · exact ⟨22159, by norm_num, by omega, by omega⟩
  by_cases h33 : n ≤ 22300
  · exact ⟨22229, by norm_num, by omega, by omega⟩
  by_cases h34 : n ≤ 22362
  · exact ⟨22291, by norm_num, by omega, by omega⟩
  by_cases h35 : n ≤ 22420
  · exact ⟨22349, by norm_num, by omega, by omega⟩
  by_cases h36 : n ≤ 22480
  · exact ⟨22409, by norm_num, by omega, by omega⟩
  · exact ⟨22481, by norm_num, by omega, by omega⟩

set_option maxHeartbeats 800000 in
