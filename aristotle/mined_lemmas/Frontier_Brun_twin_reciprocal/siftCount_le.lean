import Mathlib
import RequestProject.Brun.Final

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

/-- **Brun's theorem**: the sum of the reciprocals of the twin primes converges.

The twin primes are indexed by the subtype of naturals `p` such that both `p` and `p + 2`
are prime, and the summand is `1 / p`. -/

theorem siftCount_le (N z k : ℕ) (hk : Even k) :
    (siftCount N z : ℝ)
      ≤ (N : ℝ) * (∏ p ∈ oddPrimesLe z, (1 - 2 / (p : ℝ)))
        + (N : ℝ) * (∏ p ∈ oddPrimesLe z, (1 + 4 / (p : ℝ))) / 2 ^ (k + 1)
        + (k + 1) * (2 * z + 3) ^ k := by
  set P := oddPrimesLe z with hP
  have hprim : ∀ S ∈ P.powerset, ∀ p ∈ S, Nat.Prime p ∧ p ≠ 2 := by
    intro S hS p hp
    have := (Finset.mem_powerset.mp hS) hp
    exact ⟨oddPrimesLe_prime this, oddPrimesLe_ne_two this⟩
  -- the "main term" of each `dvdCount`
  have hm : ∀ S : Finset ℕ, (∀ p ∈ S, Nat.Prime p ∧ p ≠ 2) →
      2 ^ S.card * (N : ℝ) / (∏ p ∈ S, (p : ℝ)) = (N : ℝ) * ∏ p ∈ S, (2 / (p : ℝ)) := by
    intro S hS
    have hpos : (0 : ℝ) < ∏ p ∈ S, (p : ℝ) :=
      Finset.prod_pos (fun p hp => by exact_mod_cast (hS p hp).1.pos)
    rw [Finset.prod_div_distrib, Finset.prod_const]
    field_simp
  have hbound : ∀ j, ∀ S ∈ P.powersetCard j,
      |(dvdCount N S : ℝ) - (N : ℝ) * ∏ p ∈ S, (2 / (p : ℝ))| ≤ 2 ^ j := by
    intro j S hS
    have hSP : S ⊆ P := (Finset.mem_powersetCard.mp hS).1
    have hcard : S.card = j := (Finset.mem_powersetCard.mp hS).2
    have hprimS : ∀ p ∈ S, Nat.Prime p ∧ p ≠ 2 := fun p hp =>
      ⟨oddPrimesLe_prime (hSP hp), oddPrimesLe_ne_two (hSP hp)⟩
    have := abs_dvdCount_sub_le N S hprimS
    rwa [hm S hprimS, hcard] at this
  -- split into main term and error
  have hsplit : ∑ j ∈ range (k + 1), (-1 : ℝ) ^ j * ∑ S ∈ P.powersetCard j, (dvdCount N S : ℝ)
      = (∑ j ∈ range (k + 1), (-1 : ℝ) ^ j *
            ∑ S ∈ P.powersetCard j, ((N : ℝ) * ∏ p ∈ S, (2 / (p : ℝ))))
        + ∑ j ∈ range (k + 1), (-1 : ℝ) ^ j *
            ∑ S ∈ P.powersetCard j, ((dvdCount N S : ℝ) - (N : ℝ) * ∏ p ∈ S, (2 / (p : ℝ))) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [← mul_add, ← Finset.sum_add_distrib]
    congr 1
    exact Finset.sum_congr rfl (fun S _ => by ring)
  -- bound the error
  have herr : ∑ j ∈ range (k + 1), (-1 : ℝ) ^ j *
      ∑ S ∈ P.powersetCard j, ((dvdCount N S : ℝ) - (N : ℝ) * ∏ p ∈ S, (2 / (p : ℝ)))
        ≤ (k + 1) * (2 * z + 3) ^ k := by
    have h1 : |∑ j ∈ range (k + 1), (-1 : ℝ) ^ j *
        ∑ S ∈ P.powersetCard j, ((dvdCount N S : ℝ) - (N : ℝ) * ∏ p ∈ S, (2 / (p : ℝ)))|
          ≤ ∑ j ∈ range (k + 1), ((P.card.choose j : ℝ) * 2 ^ j) := by
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum (fun j _ => ?_))
      rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
      refine le_trans (Finset.sum_le_sum (fun S hS => hbound j S hS)) ?_
      rw [Finset.sum_const, Finset.card_powersetCard, nsmul_eq_mul]
    have h2 : ∀ j ∈ range (k + 1), ((P.card.choose j : ℝ) * 2 ^ j) ≤ (2 * z + 3) ^ k := by
      intro j hj
      simp only [Finset.mem_range] at hj
      have hPcard : P.card ≤ z + 1 := by
        have : P ⊆ range (z + 1) := by
          intro p hp
          simp only [Finset.mem_range]
          have := mem_oddPrimesLe.mp hp
          omega
        simpa using Finset.card_le_card this
      have hchoose : (P.card.choose j : ℝ) ≤ (P.card : ℝ) ^ j := by
        have := Nat.choose_le_pow P.card j
        exact_mod_cast this
      have hstep : ((P.card : ℝ)) * 2 ≤ 2 * z + 3 := by
        have : (P.card : ℝ) ≤ (z : ℝ) + 1 := by exact_mod_cast hPcard
        linarith
      calc (P.card.choose j : ℝ) * 2 ^ j ≤ (P.card : ℝ) ^ j * 2 ^ j := by
            have : (0 : ℝ) ≤ 2 ^ j := by positivity
            nlinarith [hchoose]
        _ = ((P.card : ℝ) * 2) ^ j := by rw [mul_pow]
        _ ≤ (2 * z + 3) ^ j := by
            apply pow_le_pow_left₀ (by positivity) hstep
        _ ≤ (2 * z + 3) ^ k := by
            refine pow_le_pow_right₀ ?_ (by omega)
            have : (0 : ℝ) ≤ (z : ℝ) := Nat.cast_nonneg z
            linarith
    have h3 : ∑ j ∈ range (k + 1), ((P.card.choose j : ℝ) * 2 ^ j) ≤ (k + 1) * (2 * z + 3) ^ k := by
      calc ∑ j ∈ range (k + 1), ((P.card.choose j : ℝ) * 2 ^ j)
          ≤ ∑ _j ∈ range (k + 1), ((2 * z + 3 : ℝ) ^ k) := Finset.sum_le_sum h2
        _ = (k + 1) * (2 * z + 3) ^ k := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
            push_cast
            ring
    calc _ ≤ |∑ j ∈ range (k + 1), (-1 : ℝ) ^ j *
        ∑ S ∈ P.powersetCard j, ((dvdCount N S : ℝ) - (N : ℝ) * ∏ p ∈ S, (2 / (p : ℝ)))| :=
          le_abs_self _
      _ ≤ _ := le_trans h1 h3
  -- bound the main term
  have hmain : ∑ j ∈ range (k + 1), (-1 : ℝ) ^ j *
      ∑ S ∈ P.powersetCard j, ((N : ℝ) * ∏ p ∈ S, (2 / (p : ℝ)))
        ≤ (N : ℝ) * (∏ p ∈ P, (1 - 2 / (p : ℝ)))
          + (N : ℝ) * (∏ p ∈ P, (1 + 4 / (p : ℝ))) / 2 ^ (k + 1) := by
    have hfac : ∑ j ∈ range (k + 1), (-1 : ℝ) ^ j *
        ∑ S ∈ P.powersetCard j, ((N : ℝ) * ∏ p ∈ S, (2 / (p : ℝ)))
          = (N : ℝ) * ∑ j ∈ range (k + 1), (-1 : ℝ) ^ j *
              ∑ S ∈ P.powersetCard j, ∏ p ∈ S, (2 / (p : ℝ)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [← Finset.mul_sum]
      ring
    rw [hfac]
    have ha : ∀ p ∈ P, (0 : ℝ) ≤ 2 / (p : ℝ) := by
      intro p hp
      have : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast oddPrimesLe_three_le hp
      positivity
    have := truncated_alt_sum_le P (fun p => 2 / (p : ℝ)) ha k
    have hNnn : (0 : ℝ) ≤ (N : ℝ) := by positivity
    have hmul := mul_le_mul_of_nonneg_left this hNnn
    have heq : ∏ p ∈ P, (1 + 2 * (2 / (p : ℝ))) = ∏ p ∈ P, (1 + 4 / (p : ℝ)) := by
      refine Finset.prod_congr rfl (fun p _ => by ring)
    rw [heq] at hmul
    calc (N : ℝ) * ∑ j ∈ range (k + 1), (-1 : ℝ) ^ j *
          ∑ S ∈ P.powersetCard j, ∏ p ∈ S, (2 / (p : ℝ))
        ≤ (N : ℝ) * ((∏ p ∈ P, (1 - 2 / (p : ℝ)))
            + (∏ p ∈ P, (1 + 4 / (p : ℝ))) / 2 ^ (k + 1)) := hmul
      _ = _ := by ring
  have := siftCount_le_bonferroni N z k hk
  rw [hsplit] at this
  linarith

/-- Brun's sieve bound for the twin prime counting function. -/
