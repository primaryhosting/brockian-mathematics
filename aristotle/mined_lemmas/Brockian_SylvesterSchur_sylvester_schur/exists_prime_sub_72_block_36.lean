import Mathlib
import SylvesterSchurCore
namespace Brockian.SylvesterSchur
/-- Sylvester–Schur: for n > k ≥ 1, some element of {n+1,…,n+k} has a prime factor > k. -/

lemma exists_prime_sub_72_block_36 (n : ℕ) (hlo : 90001 ≤ n) (hhi : n ≤ 92500) :
    ∃ p : ℕ, p.Prime ∧ n - 72 < p ∧ p ≤ n := by
  by_cases h0 : n ≤ 90072
  · exact ⟨90001, by norm_num, by omega, by omega⟩
  by_cases h1 : n ≤ 90144
  · exact ⟨90073, by norm_num, by omega, by omega⟩
  by_cases h2 : n ≤ 90198
  · exact ⟨90127, by norm_num, by omega, by omega⟩
  by_cases h3 : n ≤ 90270
  · exact ⟨90199, by norm_num, by omega, by omega⟩
  by_cases h4 : n ≤ 90342
  · exact ⟨90271, by norm_num, by omega, by omega⟩
  by_cases h5 : n ≤ 90384
  · exact ⟨90313, by norm_num, by omega, by omega⟩
  by_cases h6 : n ≤ 90450
  · exact ⟨90379, by norm_num, by omega, by omega⟩
  by_cases h7 : n ≤ 90510
  · exact ⟨90439, by norm_num, by omega, by omega⟩
  by_cases h8 : n ≤ 90582
  · exact ⟨90511, by norm_num, by omega, by omega⟩
  by_cases h9 : n ≤ 90654
  · exact ⟨90583, by norm_num, by omega, by omega⟩
  by_cases h10 : n ≤ 90718
  · exact ⟨90647, by norm_num, by omega, by omega⟩
  by_cases h11 : n ≤ 90780
  · exact ⟨90709, by norm_num, by omega, by omega⟩
  by_cases h12 : n ≤ 90820
  · exact ⟨90749, by norm_num, by omega, by omega⟩
  by_cases h13 : n ≤ 90892
  · exact ⟨90821, by norm_num, by omega, by omega⟩
  by_cases h14 : n ≤ 90958
  · exact ⟨90887, by norm_num, by omega, by omega⟩
  by_cases h15 : n ≤ 91018
  · exact ⟨90947, by norm_num, by omega, by omega⟩
  by_cases h16 : n ≤ 91090
  · exact ⟨91019, by norm_num, by omega, by omega⟩
  by_cases h17 : n ≤ 91152
  · exact ⟨91081, by norm_num, by omega, by omega⟩
  by_cases h18 : n ≤ 91224
  · exact ⟨91153, by norm_num, by omega, by omega⟩
  by_cases h19 : n ≤ 91270
  · exact ⟨91199, by norm_num, by omega, by omega⟩
  by_cases h20 : n ≤ 91324
  · exact ⟨91253, by norm_num, by omega, by omega⟩
  by_cases h21 : n ≤ 91380
  · exact ⟨91309, by norm_num, by omega, by omega⟩
  by_cases h22 : n ≤ 91452
  · exact ⟨91381, by norm_num, by omega, by omega⟩
  by_cases h23 : n ≤ 91524
  · exact ⟨91453, by norm_num, by omega, by omega⟩
  by_cases h24 : n ≤ 91584
  · exact ⟨91513, by norm_num, by omega, by omega⟩
  by_cases h25 : n ≤ 91654
  · exact ⟨91583, by norm_num, by omega, by omega⟩
  by_cases h26 : n ≤ 91710
  · exact ⟨91639, by norm_num, by omega, by omega⟩
  by_cases h27 : n ≤ 91782
  · exact ⟨91711, by norm_num, by omega, by omega⟩
  by_cases h28 : n ≤ 91852
  · exact ⟨91781, by norm_num, by omega, by omega⟩
  by_cases h29 : n ≤ 91912
  · exact ⟨91841, by norm_num, by omega, by omega⟩
  by_cases h30 : n ≤ 91980
  · exact ⟨91909, by norm_num, by omega, by omega⟩
  by_cases h31 : n ≤ 92040
  · exact ⟨91969, by norm_num, by omega, by omega⟩
  by_cases h32 : n ≤ 92112
  · exact ⟨92041, by norm_num, by omega, by omega⟩
  by_cases h33 : n ≤ 92182
  · exact ⟨92111, by norm_num, by omega, by omega⟩
  by_cases h34 : n ≤ 92250
  · exact ⟨92179, by norm_num, by omega, by omega⟩
  by_cases h35 : n ≤ 92322
  · exact ⟨92251, by norm_num, by omega, by omega⟩
  by_cases h36 : n ≤ 92388
  · exact ⟨92317, by norm_num, by omega, by omega⟩
  by_cases h37 : n ≤ 92458
  · exact ⟨92387, by norm_num, by omega, by omega⟩
  · exact ⟨92459, by norm_num, by omega, by omega⟩

set_option maxHeartbeats 800000 in
