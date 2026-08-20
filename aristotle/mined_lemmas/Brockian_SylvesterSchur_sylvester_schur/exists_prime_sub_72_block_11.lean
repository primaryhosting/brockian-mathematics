import Mathlib
import SylvesterSchurCore
namespace Brockian.SylvesterSchur
/-- Sylvester–Schur: for n > k ≥ 1, some element of {n+1,…,n+k} has a prime factor > k. -/

lemma exists_prime_sub_72_block_11 (n : ℕ) (hlo : 27501 ≤ n) (hhi : n ≤ 30000) :
    ∃ p : ℕ, p.Prime ∧ n - 72 < p ∧ p ≤ n := by
  by_cases h0 : n ≤ 27558
  · exact ⟨27487, by norm_num, by omega, by omega⟩
  by_cases h1 : n ≤ 27622
  · exact ⟨27551, by norm_num, by omega, by omega⟩
  by_cases h2 : n ≤ 27688
  · exact ⟨27617, by norm_num, by omega, by omega⟩
  by_cases h3 : n ≤ 27760
  · exact ⟨27689, by norm_num, by omega, by omega⟩
  by_cases h4 : n ≤ 27822
  · exact ⟨27751, by norm_num, by omega, by omega⟩
  by_cases h5 : n ≤ 27894
  · exact ⟨27823, by norm_num, by omega, by omega⟩
  by_cases h6 : n ≤ 27964
  · exact ⟨27893, by norm_num, by omega, by omega⟩
  by_cases h7 : n ≤ 28032
  · exact ⟨27961, by norm_num, by omega, by omega⟩
  by_cases h8 : n ≤ 28102
  · exact ⟨28031, by norm_num, by omega, by omega⟩
  by_cases h9 : n ≤ 28170
  · exact ⟨28099, by norm_num, by omega, by omega⟩
  by_cases h10 : n ≤ 28234
  · exact ⟨28163, by norm_num, by omega, by omega⟩
  by_cases h11 : n ≤ 28300
  · exact ⟨28229, by norm_num, by omega, by omega⟩
  by_cases h12 : n ≤ 28368
  · exact ⟨28297, by norm_num, by omega, by omega⟩
  by_cases h13 : n ≤ 28422
  · exact ⟨28351, by norm_num, by omega, by omega⟩
  by_cases h14 : n ≤ 28482
  · exact ⟨28411, by norm_num, by omega, by omega⟩
  by_cases h15 : n ≤ 28548
  · exact ⟨28477, by norm_num, by omega, by omega⟩
  by_cases h16 : n ≤ 28620
  · exact ⟨28549, by norm_num, by omega, by omega⟩
  by_cases h17 : n ≤ 28692
  · exact ⟨28621, by norm_num, by omega, by omega⟩
  by_cases h18 : n ≤ 28758
  · exact ⟨28687, by norm_num, by omega, by omega⟩
  by_cases h19 : n ≤ 28830
  · exact ⟨28759, by norm_num, by omega, by omega⟩
  by_cases h20 : n ≤ 28888
  · exact ⟨28817, by norm_num, by omega, by omega⟩
  by_cases h21 : n ≤ 28950
  · exact ⟨28879, by norm_num, by omega, by omega⟩
  by_cases h22 : n ≤ 29020
  · exact ⟨28949, by norm_num, by omega, by omega⟩
  by_cases h23 : n ≤ 29092
  · exact ⟨29021, by norm_num, by omega, by omega⟩
  by_cases h24 : n ≤ 29148
  · exact ⟨29077, by norm_num, by omega, by omega⟩
  by_cases h25 : n ≤ 29218
  · exact ⟨29147, by norm_num, by omega, by omega⟩
  by_cases h26 : n ≤ 29280
  · exact ⟨29209, by norm_num, by omega, by omega⟩
  by_cases h27 : n ≤ 29340
  · exact ⟨29269, by norm_num, by omega, by omega⟩
  by_cases h28 : n ≤ 29410
  · exact ⟨29339, by norm_num, by omega, by omega⟩
  by_cases h29 : n ≤ 29482
  · exact ⟨29411, by norm_num, by omega, by omega⟩
  by_cases h30 : n ≤ 29554
  · exact ⟨29483, by norm_num, by omega, by omega⟩
  by_cases h31 : n ≤ 29608
  · exact ⟨29537, by norm_num, by omega, by omega⟩
  by_cases h32 : n ≤ 29670
  · exact ⟨29599, by norm_num, by omega, by omega⟩
  by_cases h33 : n ≤ 29742
  · exact ⟨29671, by norm_num, by omega, by omega⟩
  by_cases h34 : n ≤ 29812
  · exact ⟨29741, by norm_num, by omega, by omega⟩
  by_cases h35 : n ≤ 29874
  · exact ⟨29803, by norm_num, by omega, by omega⟩
  by_cases h36 : n ≤ 29944
  · exact ⟨29873, by norm_num, by omega, by omega⟩
  by_cases h37 : n ≤ 29998
  · exact ⟨29927, by norm_num, by omega, by omega⟩
  · exact ⟨29989, by norm_num, by omega, by omega⟩

set_option maxHeartbeats 800000 in
