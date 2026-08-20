import Mathlib
import SylvesterSchurCore
namespace Brockian.SylvesterSchur
/-- Sylvester–Schur: for n > k ≥ 1, some element of {n+1,…,n+k} has a prime factor > k. -/

lemma exists_prime_sub_72_block_40 (n : ℕ) (hlo : 100001 ≤ n) (hhi : n ≤ 102500) :
    ∃ p : ℕ, p.Prime ∧ n - 72 < p ∧ p ≤ n := by
  by_cases h0 : n ≤ 100062
  · exact ⟨99991, by norm_num, by omega, by omega⟩
  by_cases h1 : n ≤ 100128
  · exact ⟨100057, by norm_num, by omega, by omega⟩
  by_cases h2 : n ≤ 100200
  · exact ⟨100129, by norm_num, by omega, by omega⟩
  by_cases h3 : n ≤ 100264
  · exact ⟨100193, by norm_num, by omega, by omega⟩
  by_cases h4 : n ≤ 100308
  · exact ⟨100237, by norm_num, by omega, by omega⟩
  by_cases h5 : n ≤ 100368
  · exact ⟨100297, by norm_num, by omega, by omega⟩
  by_cases h6 : n ≤ 100434
  · exact ⟨100363, by norm_num, by omega, by omega⟩
  by_cases h7 : n ≤ 100488
  · exact ⟨100417, by norm_num, by omega, by omega⟩
  by_cases h8 : n ≤ 100554
  · exact ⟨100483, by norm_num, by omega, by omega⟩
  by_cases h9 : n ≤ 100620
  · exact ⟨100549, by norm_num, by omega, by omega⟩
  by_cases h10 : n ≤ 100692
  · exact ⟨100621, by norm_num, by omega, by omega⟩
  by_cases h11 : n ≤ 100764
  · exact ⟨100693, by norm_num, by omega, by omega⟩
  by_cases h12 : n ≤ 100818
  · exact ⟨100747, by norm_num, by omega, by omega⟩
  by_cases h13 : n ≤ 100882
  · exact ⟨100811, by norm_num, by omega, by omega⟩
  by_cases h14 : n ≤ 100924
  · exact ⟨100853, by norm_num, by omega, by omega⟩
  by_cases h15 : n ≤ 100984
  · exact ⟨100913, by norm_num, by omega, by omega⟩
  by_cases h16 : n ≤ 101052
  · exact ⟨100981, by norm_num, by omega, by omega⟩
  by_cases h17 : n ≤ 101122
  · exact ⟨101051, by norm_num, by omega, by omega⟩
  by_cases h18 : n ≤ 101190
  · exact ⟨101119, by norm_num, by omega, by omega⟩
  by_cases h19 : n ≤ 101254
  · exact ⟨101183, by norm_num, by omega, by omega⟩
  by_cases h20 : n ≤ 101292
  · exact ⟨101221, by norm_num, by omega, by omega⟩
  by_cases h21 : n ≤ 101364
  · exact ⟨101293, by norm_num, by omega, by omega⟩
  by_cases h22 : n ≤ 101434
  · exact ⟨101363, by norm_num, by omega, by omega⟩
  by_cases h23 : n ≤ 101500
  · exact ⟨101429, by norm_num, by omega, by omega⟩
  by_cases h24 : n ≤ 101572
  · exact ⟨101501, by norm_num, by omega, by omega⟩
  by_cases h25 : n ≤ 101644
  · exact ⟨101573, by norm_num, by omega, by omega⟩
  by_cases h26 : n ≤ 101712
  · exact ⟨101641, by norm_num, by omega, by omega⟩
  by_cases h27 : n ≤ 101772
  · exact ⟨101701, by norm_num, by omega, by omega⟩
  by_cases h28 : n ≤ 101842
  · exact ⟨101771, by norm_num, by omega, by omega⟩
  by_cases h29 : n ≤ 101910
  · exact ⟨101839, by norm_num, by omega, by omega⟩
  by_cases h30 : n ≤ 101962
  · exact ⟨101891, by norm_num, by omega, by omega⟩
  by_cases h31 : n ≤ 102034
  · exact ⟨101963, by norm_num, by omega, by omega⟩
  by_cases h32 : n ≤ 102102
  · exact ⟨102031, by norm_num, by omega, by omega⟩
  by_cases h33 : n ≤ 102174
  · exact ⟨102103, by norm_num, by omega, by omega⟩
  by_cases h34 : n ≤ 102232
  · exact ⟨102161, by norm_num, by omega, by omega⟩
  by_cases h35 : n ≤ 102304
  · exact ⟨102233, by norm_num, by omega, by omega⟩
  by_cases h36 : n ≤ 102372
  · exact ⟨102301, by norm_num, by omega, by omega⟩
  by_cases h37 : n ≤ 102438
  · exact ⟨102367, by norm_num, by omega, by omega⟩
  · exact ⟨102437, by norm_num, by omega, by omega⟩

set_option maxHeartbeats 800000 in
