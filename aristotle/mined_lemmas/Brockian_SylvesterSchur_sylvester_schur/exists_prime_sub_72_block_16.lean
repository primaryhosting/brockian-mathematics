import Mathlib
import SylvesterSchurCore
namespace Brockian.SylvesterSchur
/-- Sylvester–Schur: for n > k ≥ 1, some element of {n+1,…,n+k} has a prime factor > k. -/

lemma exists_prime_sub_72_block_16 (n : ℕ) (hlo : 40001 ≤ n) (hhi : n ≤ 42500) :
    ∃ p : ℕ, p.Prime ∧ n - 72 < p ∧ p ≤ n := by
  by_cases h0 : n ≤ 40060
  · exact ⟨39989, by norm_num, by omega, by omega⟩
  by_cases h1 : n ≤ 40110
  · exact ⟨40039, by norm_num, by omega, by omega⟩
  by_cases h2 : n ≤ 40182
  · exact ⟨40111, by norm_num, by omega, by omega⟩
  by_cases h3 : n ≤ 40248
  · exact ⟨40177, by norm_num, by omega, by omega⟩
  by_cases h4 : n ≤ 40312
  · exact ⟨40241, by norm_num, by omega, by omega⟩
  by_cases h5 : n ≤ 40360
  · exact ⟨40289, by norm_num, by omega, by omega⟩
  by_cases h6 : n ≤ 40432
  · exact ⟨40361, by norm_num, by omega, by omega⟩
  by_cases h7 : n ≤ 40504
  · exact ⟨40433, by norm_num, by omega, by omega⟩
  by_cases h8 : n ≤ 40570
  · exact ⟨40499, by norm_num, by omega, by omega⟩
  by_cases h9 : n ≤ 40630
  · exact ⟨40559, by norm_num, by omega, by omega⟩
  by_cases h10 : n ≤ 40698
  · exact ⟨40627, by norm_num, by omega, by omega⟩
  by_cases h11 : n ≤ 40770
  · exact ⟨40699, by norm_num, by omega, by omega⟩
  by_cases h12 : n ≤ 40842
  · exact ⟨40771, by norm_num, by omega, by omega⟩
  by_cases h13 : n ≤ 40912
  · exact ⟨40841, by norm_num, by omega, by omega⟩
  by_cases h14 : n ≤ 40974
  · exact ⟨40903, by norm_num, by omega, by omega⟩
  by_cases h15 : n ≤ 41044
  · exact ⟨40973, by norm_num, by omega, by omega⟩
  by_cases h16 : n ≤ 41110
  · exact ⟨41039, by norm_num, by omega, by omega⟩
  by_cases h17 : n ≤ 41152
  · exact ⟨41081, by norm_num, by omega, by omega⟩
  by_cases h18 : n ≤ 41220
  · exact ⟨41149, by norm_num, by omega, by omega⟩
  by_cases h19 : n ≤ 41292
  · exact ⟨41221, by norm_num, by omega, by omega⟩
  by_cases h20 : n ≤ 41352
  · exact ⟨41281, by norm_num, by omega, by omega⟩
  by_cases h21 : n ≤ 41422
  · exact ⟨41351, by norm_num, by omega, by omega⟩
  by_cases h22 : n ≤ 41484
  · exact ⟨41413, by norm_num, by omega, by omega⟩
  by_cases h23 : n ≤ 41550
  · exact ⟨41479, by norm_num, by omega, by omega⟩
  by_cases h24 : n ≤ 41620
  · exact ⟨41549, by norm_num, by omega, by omega⟩
  by_cases h25 : n ≤ 41692
  · exact ⟨41621, by norm_num, by omega, by omega⟩
  by_cases h26 : n ≤ 41758
  · exact ⟨41687, by norm_num, by omega, by omega⟩
  by_cases h27 : n ≤ 41830
  · exact ⟨41759, by norm_num, by omega, by omega⟩
  by_cases h28 : n ≤ 41884
  · exact ⟨41813, by norm_num, by omega, by omega⟩
  by_cases h29 : n ≤ 41950
  · exact ⟨41879, by norm_num, by omega, by omega⟩
  by_cases h30 : n ≤ 42018
  · exact ⟨41947, by norm_num, by omega, by omega⟩
  by_cases h31 : n ≤ 42090
  · exact ⟨42019, by norm_num, by omega, by omega⟩
  by_cases h32 : n ≤ 42160
  · exact ⟨42089, by norm_num, by omega, by omega⟩
  by_cases h33 : n ≤ 42228
  · exact ⟨42157, by norm_num, by omega, by omega⟩
  by_cases h34 : n ≤ 42298
  · exact ⟨42227, by norm_num, by omega, by omega⟩
  by_cases h35 : n ≤ 42370
  · exact ⟨42299, by norm_num, by omega, by omega⟩
  by_cases h36 : n ≤ 42430
  · exact ⟨42359, by norm_num, by omega, by omega⟩
  by_cases h37 : n ≤ 42480
  · exact ⟨42409, by norm_num, by omega, by omega⟩
  · exact ⟨42473, by norm_num, by omega, by omega⟩

set_option maxHeartbeats 800000 in
