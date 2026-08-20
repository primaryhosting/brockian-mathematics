import Mathlib

/-!
# Coprime Same Parity Twenty One Prime Factors
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.coprime_sameParity_twentyOne_primeFactors
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Nat

set_option maxHeartbeats 4000000
set_option maxRecDepth 40000

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Brockian.BetrothedNumbers

open ArithmeticFunction

/-! ## The definition -/

/-- A *betrothed* (quasi-amicable) pair: two positive integers each of whose sum of
divisors equals the sum of the two numbers plus one, i.e. `σ₁(m) = σ₁(n) = m + n + 1`. -/

lemma prod_lt_four_of_card_le_twenty {S : Finset ℕ}
    (hS : ∀ p ∈ S, p.Prime ∧ p ≠ 2) (hcard : S.card ≤ 20) :
    ∏ p ∈ S, (p : ℚ) / (p - 1) < 4 := by
  classical
  set A := smallOddPrimes with hA
  set f : ℕ → ℚ := fun p => (p : ℚ) / (p - 1) with hf
  set T := S.filter (fun p => p ≤ 73) with hT
  set U := S.filter (fun p => ¬ p ≤ 73) with hU
  have hfpos : ∀ p : ℕ, 2 ≤ p → 0 < f p := by
    intro p hp
    have h2 : (2 : ℚ) ≤ (p : ℚ) := by exact_mod_cast hp
    exact div_pos (by linarith) (by linarith)
  have hTA : T ⊆ A := by
    intro p hp
    rw [hT, Finset.mem_filter] at hp
    obtain ⟨hpS, hple⟩ := hp
    obtain ⟨hpp, hp2⟩ := hS p hpS
    have hall : ∀ q ∈ Finset.range 74, Nat.Prime q → q ≠ 2 → q ∈ smallOddPrimes := by decide
    exact hall p (Finset.mem_range.mpr (by omega)) hpp hp2
  have hTnonneg : 0 ≤ ∏ p ∈ T, f p := by
    refine Finset.prod_nonneg fun p hp => ?_
    rw [hT, Finset.mem_filter] at hp
    exact le_of_lt (hfpos p (hS p hp.1).1.two_le)
  have hUbound : ∏ p ∈ U, f p ≤ (74 / 73 : ℚ) ^ U.card := by
    rw [← Finset.prod_const]
    refine Finset.prod_le_prod (fun p hp => ?_) (fun p hp => ?_)
    · rw [hU, Finset.mem_filter] at hp
      exact le_of_lt (hfpos p (hS p hp.1).1.two_le)
    · rw [hU, Finset.mem_filter] at hp
      have hp74 : (74 : ℚ) ≤ (p : ℚ) := by exact_mod_cast (by omega : 74 ≤ p)
      show (p : ℚ) / (p - 1) ≤ 74 / 73
      rw [div_le_div_iff₀ (by linarith) (by norm_num)]
      linarith
  have hAdiff : (73 / 72 : ℚ) ^ ((A \ T).card) ≤ ∏ p ∈ A \ T, f p := by
    rw [← Finset.prod_const]
    refine Finset.prod_le_prod (fun p _ => by norm_num) (fun p hp => ?_)
    have hpA : p ∈ A := (Finset.mem_sdiff.mp hp).1
    have hb : ∀ q ∈ smallOddPrimes, 3 ≤ q ∧ q ≤ 73 := by decide
    obtain ⟨h3, h73⟩ := hb p hpA
    have h3' : (3 : ℚ) ≤ (p : ℚ) := by exact_mod_cast h3
    have h73' : (p : ℚ) ≤ 73 := by exact_mod_cast h73
    show (73 / 72 : ℚ) ≤ (p : ℚ) / (p - 1)
    rw [div_le_div_iff₀ (by norm_num) (by linarith)]
    linarith
  have hcards : U.card ≤ (A \ T).card := by
    have h1 : (A \ T).card = A.card - T.card := Finset.card_sdiff_of_subset hTA
    have h2 : A.card = 20 := by decide
    have h3 : T.card + U.card = S.card := Finset.card_filter_add_card_filter_not _
    have h4 : T.card ≤ A.card := Finset.card_le_card hTA
    omega
  have hpow : (74 / 73 : ℚ) ^ U.card ≤ (73 / 72 : ℚ) ^ ((A \ T).card) :=
    calc (74 / 73 : ℚ) ^ U.card ≤ (73 / 72 : ℚ) ^ U.card :=
          pow_le_pow_left₀ (by norm_num) (by norm_num) _
      _ ≤ (73 / 72 : ℚ) ^ ((A \ T).card) := pow_le_pow_right₀ (by norm_num) hcards
  calc ∏ p ∈ S, f p = (∏ p ∈ T, f p) * ∏ p ∈ U, f p :=
        (Finset.prod_filter_mul_prod_filter_not S _ f).symm
    _ ≤ (∏ p ∈ T, f p) * (74 / 73 : ℚ) ^ U.card := mul_le_mul_of_nonneg_left hUbound hTnonneg
    _ ≤ (∏ p ∈ T, f p) * (73 / 72 : ℚ) ^ ((A \ T).card) :=
        mul_le_mul_of_nonneg_left hpow hTnonneg
    _ ≤ (∏ p ∈ T, f p) * ∏ p ∈ A \ T, f p := mul_le_mul_of_nonneg_left hAdiff hTnonneg
    _ = ∏ p ∈ A, f p := by rw [mul_comm]; exact Finset.prod_sdiff hTA
    _ < 4 := prod_smallOddPrimes_lt_four

/-! ## The abundancy of a coprime betrothed pair -/

/-- For a coprime betrothed pair the abundancy bound of the product exceeds `4`. -/
