import Mathlib
import SylvesterSchurCore
namespace Brockian.SylvesterSchur
/-- Sylvester–Schur: for n > k ≥ 1, some element of {n+1,…,n+k} has a prime factor > k. -/

lemma exists_prime_sub_72_le_of_le_125000 (n : ℕ) (hlo : 144 ≤ n)
    (hhi : n ≤ 125000) :
    ∃ p : ℕ, p.Prime ∧ n - 72 < p ∧ p ≤ n := by
  by_cases h0 : n ≤ 2500
  · exact exists_prime_sub_72_block_0 n (by omega) h0
  by_cases h1 : n ≤ 5000
  · exact exists_prime_sub_72_block_1 n (by omega) h1
  by_cases h2 : n ≤ 7500
  · exact exists_prime_sub_72_block_2 n (by omega) h2
  by_cases h3 : n ≤ 10000
  · exact exists_prime_sub_72_block_3 n (by omega) h3
  by_cases h4 : n ≤ 12500
  · exact exists_prime_sub_72_block_4 n (by omega) h4
  by_cases h5 : n ≤ 15000
  · exact exists_prime_sub_72_block_5 n (by omega) h5
  by_cases h6 : n ≤ 17500
  · exact exists_prime_sub_72_block_6 n (by omega) h6
  by_cases h7 : n ≤ 20000
  · exact exists_prime_sub_72_block_7 n (by omega) h7
  by_cases h8 : n ≤ 22500
  · exact exists_prime_sub_72_block_8 n (by omega) h8
  by_cases h9 : n ≤ 25000
  · exact exists_prime_sub_72_block_9 n (by omega) h9
  by_cases h10 : n ≤ 27500
  · exact exists_prime_sub_72_block_10 n (by omega) h10
  by_cases h11 : n ≤ 30000
  · exact exists_prime_sub_72_block_11 n (by omega) h11
  by_cases h12 : n ≤ 32500
  · exact exists_prime_sub_72_block_12 n (by omega) h12
  by_cases h13 : n ≤ 35000
  · exact exists_prime_sub_72_block_13 n (by omega) h13
  by_cases h14 : n ≤ 37500
  · exact exists_prime_sub_72_block_14 n (by omega) h14
  by_cases h15 : n ≤ 40000
  · exact exists_prime_sub_72_block_15 n (by omega) h15
  by_cases h16 : n ≤ 42500
  · exact exists_prime_sub_72_block_16 n (by omega) h16
  by_cases h17 : n ≤ 45000
  · exact exists_prime_sub_72_block_17 n (by omega) h17
  by_cases h18 : n ≤ 47500
  · exact exists_prime_sub_72_block_18 n (by omega) h18
  by_cases h19 : n ≤ 50000
  · exact exists_prime_sub_72_block_19 n (by omega) h19
  by_cases h20 : n ≤ 52500
  · exact exists_prime_sub_72_block_20 n (by omega) h20
  by_cases h21 : n ≤ 55000
  · exact exists_prime_sub_72_block_21 n (by omega) h21
  by_cases h22 : n ≤ 57500
  · exact exists_prime_sub_72_block_22 n (by omega) h22
  by_cases h23 : n ≤ 60000
  · exact exists_prime_sub_72_block_23 n (by omega) h23
  by_cases h24 : n ≤ 62500
  · exact exists_prime_sub_72_block_24 n (by omega) h24
  by_cases h25 : n ≤ 65000
  · exact exists_prime_sub_72_block_25 n (by omega) h25
  by_cases h26 : n ≤ 67500
  · exact exists_prime_sub_72_block_26 n (by omega) h26
  by_cases h27 : n ≤ 70000
  · exact exists_prime_sub_72_block_27 n (by omega) h27
  by_cases h28 : n ≤ 72500
  · exact exists_prime_sub_72_block_28 n (by omega) h28
  by_cases h29 : n ≤ 75000
  · exact exists_prime_sub_72_block_29 n (by omega) h29
  by_cases h30 : n ≤ 77500
  · exact exists_prime_sub_72_block_30 n (by omega) h30
  by_cases h31 : n ≤ 80000
  · exact exists_prime_sub_72_block_31 n (by omega) h31
  by_cases h32 : n ≤ 82500
  · exact exists_prime_sub_72_block_32 n (by omega) h32
  by_cases h33 : n ≤ 85000
  · exact exists_prime_sub_72_block_33 n (by omega) h33
  by_cases h34 : n ≤ 87500
  · exact exists_prime_sub_72_block_34 n (by omega) h34
  by_cases h35 : n ≤ 90000
  · exact exists_prime_sub_72_block_35 n (by omega) h35
  by_cases h36 : n ≤ 92500
  · exact exists_prime_sub_72_block_36 n (by omega) h36
  by_cases h37 : n ≤ 95000
  · exact exists_prime_sub_72_block_37 n (by omega) h37
  by_cases h38 : n ≤ 97500
  · exact exists_prime_sub_72_block_38 n (by omega) h38
  by_cases h39 : n ≤ 100000
  · exact exists_prime_sub_72_block_39 n (by omega) h39
  by_cases h40 : n ≤ 102500
  · exact exists_prime_sub_72_block_40 n (by omega) h40
  by_cases h41 : n ≤ 105000
  · exact exists_prime_sub_72_block_41 n (by omega) h41
  by_cases h42 : n ≤ 107500
  · exact exists_prime_sub_72_block_42 n (by omega) h42
  by_cases h43 : n ≤ 110000
  · exact exists_prime_sub_72_block_43 n (by omega) h43
  by_cases h44 : n ≤ 112500
  · exact exists_prime_sub_72_block_44 n (by omega) h44
  by_cases h45 : n ≤ 115000
  · exact exists_prime_sub_72_block_45 n (by omega) h45
  by_cases h46 : n ≤ 117500
  · exact exists_prime_sub_72_block_46 n (by omega) h46
  by_cases h47 : n ≤ 120000
  · exact exists_prime_sub_72_block_47 n (by omega) h47
  by_cases h48 : n ≤ 122500
  · exact exists_prime_sub_72_block_48 n (by omega) h48
  · exact exists_prime_sub_72_block_49 n (by omega) hhi

