import Mathlib
import SylvesterSchurCore
namespace Brockian.SylvesterSchur
/-- Sylvester–Schur: for n > k ≥ 1, some element of {n+1,…,n+k} has a prime factor > k. -/

lemma exists_prime_sub_49_le_of_le_600 (n : ℕ) (hlo : 98 ≤ n) (hhi : n ≤ 600) :
    ∃ p : ℕ, p.Prime ∧ n - 49 < p ∧ p ≤ n := by
  by_cases h0 : n ≤ 145
  · exact ⟨97, by norm_num, by omega, by omega⟩
  by_cases h1 : n ≤ 187
  · exact ⟨139, by norm_num, by omega, by omega⟩
  by_cases h2 : n ≤ 229
  · exact ⟨181, by norm_num, by omega, by omega⟩
  by_cases h3 : n ≤ 277
  · exact ⟨229, by norm_num, by omega, by omega⟩
  by_cases h4 : n ≤ 325
  · exact ⟨277, by norm_num, by omega, by omega⟩
  by_cases h5 : n ≤ 365
  · exact ⟨317, by norm_num, by omega, by omega⟩
  by_cases h6 : n ≤ 407
  · exact ⟨359, by norm_num, by omega, by omega⟩
  by_cases h7 : n ≤ 449
  · exact ⟨401, by norm_num, by omega, by omega⟩
  by_cases h8 : n ≤ 497
  · exact ⟨449, by norm_num, by omega, by omega⟩
  by_cases h9 : n ≤ 539
  · exact ⟨491, by norm_num, by omega, by omega⟩
  by_cases h10 : n ≤ 571
  · exact ⟨523, by norm_num, by omega, by omega⟩
  · exact ⟨571, by norm_num, by omega, by omega⟩

-- Prime-gap certificates, chunked to keep proof search local.
set_option maxHeartbeats 800000 in
