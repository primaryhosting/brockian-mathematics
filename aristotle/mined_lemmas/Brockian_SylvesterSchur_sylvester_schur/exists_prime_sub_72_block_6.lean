import Mathlib
import SylvesterSchurCore
namespace Brockian.SylvesterSchur
/-- Sylvester–Schur: for n > k ≥ 1, some element of {n+1,…,n+k} has a prime factor > k. -/

lemma exists_prime_sub_72_block_6 (n : ℕ) (hlo : 15001 ≤ n) (hhi : n ≤ 17500) :
    ∃ p : ℕ, p.Prime ∧ n - 72 < p ∧ p ≤ n := by
  by_cases h0 : n ≤ 15054
  · exact ⟨14983, by norm_num, by omega, by omega⟩
  by_cases h1 : n ≤ 15124
  · exact ⟨15053, by norm_num, by omega, by omega⟩
  by_cases h2 : n ≤ 15192
  · exact ⟨15121, by norm_num, by omega, by omega⟩
  by_cases h3 : n ≤ 15264
  · exact ⟨15193, by norm_num, by omega, by omega⟩
  by_cases h4 : n ≤ 15334
  · exact ⟨15263, by norm_num, by omega, by omega⟩
  by_cases h5 : n ≤ 15402
  · exact ⟨15331, by norm_num, by omega, by omega⟩
  by_cases h6 : n ≤ 15472
  · exact ⟨15401, by norm_num, by omega, by omega⟩
  by_cases h7 : n ≤ 15544
  · exact ⟨15473, by norm_num, by omega, by omega⟩
  by_cases h8 : n ≤ 15612
  · exact ⟨15541, by norm_num, by omega, by omega⟩
  by_cases h9 : n ≤ 15678
  · exact ⟨15607, by norm_num, by omega, by omega⟩
  by_cases h10 : n ≤ 15750
  · exact ⟨15679, by norm_num, by omega, by omega⟩
  by_cases h11 : n ≤ 15820
  · exact ⟨15749, by norm_num, by omega, by omega⟩
  by_cases h12 : n ≤ 15888
  · exact ⟨15817, by norm_num, by omega, by omega⟩
  by_cases h13 : n ≤ 15960
  · exact ⟨15889, by norm_num, by omega, by omega⟩
  by_cases h14 : n ≤ 16030
  · exact ⟨15959, by norm_num, by omega, by omega⟩
  by_cases h15 : n ≤ 16078
  · exact ⟨16007, by norm_num, by omega, by omega⟩
  by_cases h16 : n ≤ 16144
  · exact ⟨16073, by norm_num, by omega, by omega⟩
  by_cases h17 : n ≤ 16212
  · exact ⟨16141, by norm_num, by omega, by omega⟩
  by_cases h18 : n ≤ 16264
  · exact ⟨16193, by norm_num, by omega, by omega⟩
  by_cases h19 : n ≤ 16324
  · exact ⟨16253, by norm_num, by omega, by omega⟩
  by_cases h20 : n ≤ 16390
  · exact ⟨16319, by norm_num, by omega, by omega⟩
  by_cases h21 : n ≤ 16452
  · exact ⟨16381, by norm_num, by omega, by omega⟩
  by_cases h22 : n ≤ 16524
  · exact ⟨16453, by norm_num, by omega, by omega⟩
  by_cases h23 : n ≤ 16590
  · exact ⟨16519, by norm_num, by omega, by omega⟩
  by_cases h24 : n ≤ 16644
  · exact ⟨16573, by norm_num, by omega, by omega⟩
  by_cases h25 : n ≤ 16704
  · exact ⟨16633, by norm_num, by omega, by omega⟩
  by_cases h26 : n ≤ 16774
  · exact ⟨16703, by norm_num, by omega, by omega⟩
  by_cases h27 : n ≤ 16834
  · exact ⟨16763, by norm_num, by omega, by omega⟩
  by_cases h28 : n ≤ 16902
  · exact ⟨16831, by norm_num, by omega, by omega⟩
  by_cases h29 : n ≤ 16974
  · exact ⟨16903, by norm_num, by omega, by omega⟩
  by_cases h30 : n ≤ 17034
  · exact ⟨16963, by norm_num, by omega, by omega⟩
  by_cases h31 : n ≤ 17104
  · exact ⟨17033, by norm_num, by omega, by omega⟩
  by_cases h32 : n ≤ 17170
  · exact ⟨17099, by norm_num, by omega, by omega⟩
  by_cases h33 : n ≤ 17238
  · exact ⟨17167, by norm_num, by omega, by omega⟩
  by_cases h34 : n ≤ 17310
  · exact ⟨17239, by norm_num, by omega, by omega⟩
  by_cases h35 : n ≤ 17370
  · exact ⟨17299, by norm_num, by omega, by omega⟩
  by_cases h36 : n ≤ 17430
  · exact ⟨17359, by norm_num, by omega, by omega⟩
  · exact ⟨17431, by norm_num, by omega, by omega⟩

set_option maxHeartbeats 800000 in
