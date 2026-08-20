import Mathlib
import SylvesterSchurCore
namespace Brockian.SylvesterSchur
/-- Sylvester–Schur: for n > k ≥ 1, some element of {n+1,…,n+k} has a prime factor > k. -/

lemma exists_prime_sub_72_block_25 (n : ℕ) (hlo : 62501 ≤ n) (hhi : n ≤ 65000) :
    ∃ p : ℕ, p.Prime ∧ n - 72 < p ∧ p ≤ n := by
  by_cases h0 : n ≤ 62572
  · exact ⟨62501, by norm_num, by omega, by omega⟩
  by_cases h1 : n ≤ 62634
  · exact ⟨62563, by norm_num, by omega, by omega⟩
  by_cases h2 : n ≤ 62704
  · exact ⟨62633, by norm_num, by omega, by omega⟩
  by_cases h3 : n ≤ 62772
  · exact ⟨62701, by norm_num, by omega, by omega⟩
  by_cases h4 : n ≤ 62844
  · exact ⟨62773, by norm_num, by omega, by omega⟩
  by_cases h5 : n ≤ 62898
  · exact ⟨62827, by norm_num, by omega, by omega⟩
  by_cases h6 : n ≤ 62968
  · exact ⟨62897, by norm_num, by omega, by omega⟩
  by_cases h7 : n ≤ 63040
  · exact ⟨62969, by norm_num, by omega, by omega⟩
  by_cases h8 : n ≤ 63102
  · exact ⟨63031, by norm_num, by omega, by omega⟩
  by_cases h9 : n ≤ 63174
  · exact ⟨63103, by norm_num, by omega, by omega⟩
  by_cases h10 : n ≤ 63220
  · exact ⟨63149, by norm_num, by omega, by omega⟩
  by_cases h11 : n ≤ 63282
  · exact ⟨63211, by norm_num, by omega, by omega⟩
  by_cases h12 : n ≤ 63352
  · exact ⟨63281, by norm_num, by omega, by omega⟩
  by_cases h13 : n ≤ 63424
  · exact ⟨63353, by norm_num, by omega, by omega⟩
  by_cases h14 : n ≤ 63492
  · exact ⟨63421, by norm_num, by omega, by omega⟩
  by_cases h15 : n ≤ 63564
  · exact ⟨63493, by norm_num, by omega, by omega⟩
  by_cases h16 : n ≤ 63630
  · exact ⟨63559, by norm_num, by omega, by omega⟩
  by_cases h17 : n ≤ 63700
  · exact ⟨63629, by norm_num, by omega, by omega⟩
  by_cases h18 : n ≤ 63768
  · exact ⟨63697, by norm_num, by omega, by omega⟩
  by_cases h19 : n ≤ 63832
  · exact ⟨63761, by norm_num, by omega, by omega⟩
  by_cases h20 : n ≤ 63894
  · exact ⟨63823, by norm_num, by omega, by omega⟩
  by_cases h21 : n ≤ 63934
  · exact ⟨63863, by norm_num, by omega, by omega⟩
  by_cases h22 : n ≤ 64000
  · exact ⟨63929, by norm_num, by omega, by omega⟩
  by_cases h23 : n ≤ 64068
  · exact ⟨63997, by norm_num, by omega, by omega⟩
  by_cases h24 : n ≤ 64138
  · exact ⟨64067, by norm_num, by omega, by omega⟩
  by_cases h25 : n ≤ 64194
  · exact ⟨64123, by norm_num, by omega, by omega⟩
  by_cases h26 : n ≤ 64260
  · exact ⟨64189, by norm_num, by omega, by omega⟩
  by_cases h27 : n ≤ 64308
  · exact ⟨64237, by norm_num, by omega, by omega⟩
  by_cases h28 : n ≤ 64374
  · exact ⟨64303, by norm_num, by omega, by omega⟩
  by_cases h29 : n ≤ 64444
  · exact ⟨64373, by norm_num, by omega, by omega⟩
  by_cases h30 : n ≤ 64510
  · exact ⟨64439, by norm_num, by omega, by omega⟩
  by_cases h31 : n ≤ 64570
  · exact ⟨64499, by norm_num, by omega, by omega⟩
  by_cases h32 : n ≤ 64638
  · exact ⟨64567, by norm_num, by omega, by omega⟩
  by_cases h33 : n ≤ 64704
  · exact ⟨64633, by norm_num, by omega, by omega⟩
  by_cases h34 : n ≤ 64764
  · exact ⟨64693, by norm_num, by omega, by omega⟩
  by_cases h35 : n ≤ 64834
  · exact ⟨64763, by norm_num, by omega, by omega⟩
  by_cases h36 : n ≤ 64888
  · exact ⟨64817, by norm_num, by omega, by omega⟩
  by_cases h37 : n ≤ 64950
  · exact ⟨64879, by norm_num, by omega, by omega⟩
  · exact ⟨64951, by norm_num, by omega, by omega⟩

set_option maxHeartbeats 800000 in
