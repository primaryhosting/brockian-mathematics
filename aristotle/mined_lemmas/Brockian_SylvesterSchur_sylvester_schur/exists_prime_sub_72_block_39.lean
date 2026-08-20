import Mathlib
import SylvesterSchurCore
namespace Brockian.SylvesterSchur
/-- Sylvester–Schur: for n > k ≥ 1, some element of {n+1,…,n+k} has a prime factor > k. -/

lemma exists_prime_sub_72_block_39 (n : ℕ) (hlo : 97501 ≤ n) (hhi : n ≤ 100000) :
    ∃ p : ℕ, p.Prime ∧ n - 72 < p ∧ p ≤ n := by
  by_cases h0 : n ≤ 97572
  · exact ⟨97501, by norm_num, by omega, by omega⟩
  by_cases h1 : n ≤ 97642
  · exact ⟨97571, by norm_num, by omega, by omega⟩
  by_cases h2 : n ≤ 97684
  · exact ⟨97613, by norm_num, by omega, by omega⟩
  by_cases h3 : n ≤ 97744
  · exact ⟨97673, by norm_num, by omega, by omega⟩
  by_cases h4 : n ≤ 97800
  · exact ⟨97729, by norm_num, by omega, by omega⟩
  by_cases h5 : n ≤ 97860
  · exact ⟨97789, by norm_num, by omega, by omega⟩
  by_cases h6 : n ≤ 97932
  · exact ⟨97861, by norm_num, by omega, by omega⟩
  by_cases h7 : n ≤ 98002
  · exact ⟨97931, by norm_num, by omega, by omega⟩
  by_cases h8 : n ≤ 98058
  · exact ⟨97987, by norm_num, by omega, by omega⟩
  by_cases h9 : n ≤ 98128
  · exact ⟨98057, by norm_num, by omega, by omega⟩
  by_cases h10 : n ≤ 98200
  · exact ⟨98129, by norm_num, by omega, by omega⟩
  by_cases h11 : n ≤ 98250
  · exact ⟨98179, by norm_num, by omega, by omega⟩
  by_cases h12 : n ≤ 98322
  · exact ⟨98251, by norm_num, by omega, by omega⟩
  by_cases h13 : n ≤ 98394
  · exact ⟨98323, by norm_num, by omega, by omega⟩
  by_cases h14 : n ≤ 98460
  · exact ⟨98389, by norm_num, by omega, by omega⟩
  by_cases h15 : n ≤ 98530
  · exact ⟨98459, by norm_num, by omega, by omega⟩
  by_cases h16 : n ≤ 98590
  · exact ⟨98519, by norm_num, by omega, by omega⟩
  by_cases h17 : n ≤ 98644
  · exact ⟨98573, by norm_num, by omega, by omega⟩
  by_cases h18 : n ≤ 98712
  · exact ⟨98641, by norm_num, by omega, by omega⟩
  by_cases h19 : n ≤ 98784
  · exact ⟨98713, by norm_num, by omega, by omega⟩
  by_cases h20 : n ≤ 98850
  · exact ⟨98779, by norm_num, by omega, by omega⟩
  by_cases h21 : n ≤ 98920
  · exact ⟨98849, by norm_num, by omega, by omega⟩
  by_cases h22 : n ≤ 98982
  · exact ⟨98911, by norm_num, by omega, by omega⟩
  by_cases h23 : n ≤ 99052
  · exact ⟨98981, by norm_num, by omega, by omega⟩
  by_cases h24 : n ≤ 99124
  · exact ⟨99053, by norm_num, by omega, by omega⟩
  by_cases h25 : n ≤ 99190
  · exact ⟨99119, by norm_num, by omega, by omega⟩
  by_cases h26 : n ≤ 99262
  · exact ⟨99191, by norm_num, by omega, by omega⟩
  by_cases h27 : n ≤ 99330
  · exact ⟨99259, by norm_num, by omega, by omega⟩
  by_cases h28 : n ≤ 99388
  · exact ⟨99317, by norm_num, by omega, by omega⟩
  by_cases h29 : n ≤ 99448
  · exact ⟨99377, by norm_num, by omega, by omega⟩
  by_cases h30 : n ≤ 99510
  · exact ⟨99439, by norm_num, by omega, by omega⟩
  by_cases h31 : n ≤ 99568
  · exact ⟨99497, by norm_num, by omega, by omega⟩
  by_cases h32 : n ≤ 99634
  · exact ⟨99563, by norm_num, by omega, by omega⟩
  by_cases h33 : n ≤ 99694
  · exact ⟨99623, by norm_num, by omega, by omega⟩
  by_cases h34 : n ≤ 99760
  · exact ⟨99689, by norm_num, by omega, by omega⟩
  by_cases h35 : n ≤ 99832
  · exact ⟨99761, by norm_num, by omega, by omega⟩
  by_cases h36 : n ≤ 99904
  · exact ⟨99833, by norm_num, by omega, by omega⟩
  by_cases h37 : n ≤ 99972
  · exact ⟨99901, by norm_num, by omega, by omega⟩
  · exact ⟨99971, by norm_num, by omega, by omega⟩

set_option maxHeartbeats 800000 in
