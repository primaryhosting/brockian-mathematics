import Mathlib
import SylvesterSchurCore
namespace Brockian.SylvesterSchur
/-- Sylvester–Schur: for n > k ≥ 1, some element of {n+1,…,n+k} has a prime factor > k. -/

lemma exists_prime_sub_72_block_26 (n : ℕ) (hlo : 65001 ≤ n) (hhi : n ≤ 67500) :
    ∃ p : ℕ, p.Prime ∧ n - 72 < p ∧ p ≤ n := by
  by_cases h0 : n ≤ 65068
  · exact ⟨64997, by norm_num, by omega, by omega⟩
  by_cases h1 : n ≤ 65134
  · exact ⟨65063, by norm_num, by omega, by omega⟩
  by_cases h2 : n ≤ 65200
  · exact ⟨65129, by norm_num, by omega, by omega⟩
  by_cases h3 : n ≤ 65254
  · exact ⟨65183, by norm_num, by omega, by omega⟩
  by_cases h4 : n ≤ 65310
  · exact ⟨65239, by norm_num, by omega, by omega⟩
  by_cases h5 : n ≤ 65380
  · exact ⟨65309, by norm_num, by omega, by omega⟩
  by_cases h6 : n ≤ 65452
  · exact ⟨65381, by norm_num, by omega, by omega⟩
  by_cases h7 : n ≤ 65520
  · exact ⟨65449, by norm_num, by omega, by omega⟩
  by_cases h8 : n ≤ 65592
  · exact ⟨65521, by norm_num, by omega, by omega⟩
  by_cases h9 : n ≤ 65658
  · exact ⟨65587, by norm_num, by omega, by omega⟩
  by_cases h10 : n ≤ 65728
  · exact ⟨65657, by norm_num, by omega, by omega⟩
  by_cases h11 : n ≤ 65800
  · exact ⟨65729, by norm_num, by omega, by omega⟩
  by_cases h12 : n ≤ 65860
  · exact ⟨65789, by norm_num, by omega, by omega⟩
  by_cases h13 : n ≤ 65922
  · exact ⟨65851, by norm_num, by omega, by omega⟩
  by_cases h14 : n ≤ 65992
  · exact ⟨65921, by norm_num, by omega, by omega⟩
  by_cases h15 : n ≤ 66064
  · exact ⟨65993, by norm_num, by omega, by omega⟩
  by_cases h16 : n ≤ 66118
  · exact ⟨66047, by norm_num, by omega, by omega⟩
  by_cases h17 : n ≤ 66180
  · exact ⟨66109, by norm_num, by omega, by omega⟩
  by_cases h18 : n ≤ 66250
  · exact ⟨66179, by norm_num, by omega, by omega⟩
  by_cases h19 : n ≤ 66310
  · exact ⟨66239, by norm_num, by omega, by omega⟩
  by_cases h20 : n ≤ 66372
  · exact ⟨66301, by norm_num, by omega, by omega⟩
  by_cases h21 : n ≤ 66444
  · exact ⟨66373, by norm_num, by omega, by omega⟩
  by_cases h22 : n ≤ 66502
  · exact ⟨66431, by norm_num, by omega, by omega⟩
  by_cases h23 : n ≤ 66570
  · exact ⟨66499, by norm_num, by omega, by omega⟩
  by_cases h24 : n ≤ 66642
  · exact ⟨66571, by norm_num, by omega, by omega⟩
  by_cases h25 : n ≤ 66714
  · exact ⟨66643, by norm_num, by omega, by omega⟩
  by_cases h26 : n ≤ 66784
  · exact ⟨66713, by norm_num, by omega, by omega⟩
  by_cases h27 : n ≤ 66834
  · exact ⟨66763, by norm_num, by omega, by omega⟩
  by_cases h28 : n ≤ 66892
  · exact ⟨66821, by norm_num, by omega, by omega⟩
  by_cases h29 : n ≤ 66960
  · exact ⟨66889, by norm_num, by omega, by omega⟩
  by_cases h30 : n ≤ 67030
  · exact ⟨66959, by norm_num, by omega, by omega⟩
  by_cases h31 : n ≤ 67092
  · exact ⟨67021, by norm_num, by omega, by omega⟩
  by_cases h32 : n ≤ 67150
  · exact ⟨67079, by norm_num, by omega, by omega⟩
  by_cases h33 : n ≤ 67212
  · exact ⟨67141, by norm_num, by omega, by omega⟩
  by_cases h34 : n ≤ 67284
  · exact ⟨67213, by norm_num, by omega, by omega⟩
  by_cases h35 : n ≤ 67344
  · exact ⟨67273, by norm_num, by omega, by omega⟩
  by_cases h36 : n ≤ 67414
  · exact ⟨67343, by norm_num, by omega, by omega⟩
  by_cases h37 : n ≤ 67482
  · exact ⟨67411, by norm_num, by omega, by omega⟩
  · exact ⟨67481, by norm_num, by omega, by omega⟩

set_option maxHeartbeats 800000 in
