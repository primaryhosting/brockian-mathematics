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

lemma sum_Ico_twinIndicator_le (M : ℕ) :
    ∑ n ∈ Ico (2 ^ M) (2 ^ (M + 1)), twinIndicator n
      ≤ (twinCount (2 ^ (M + 1)) : ℝ) / 2 ^ M := by
  have h1 : ∑ n ∈ Ico (2 ^ M) (2 ^ (M + 1)), twinIndicator n
      ≤ ∑ n ∈ Ico (2 ^ M) (2 ^ (M + 1)),
          (if Nat.Prime n ∧ Nat.Prime (n + 2) then (1 : ℝ) / 2 ^ M else 0) := by
    refine Finset.sum_le_sum (fun n hn => ?_)
    simp only [Finset.mem_Ico] at hn
    unfold twinIndicator
    split
    · apply one_div_le_one_div_of_le (by positivity)
      exact_mod_cast hn.1
    · exact le_rfl
  have h2 : ∑ n ∈ Ico (2 ^ M) (2 ^ (M + 1)),
      (if Nat.Prime n ∧ Nat.Prime (n + 2) then (1 : ℝ) / 2 ^ M else 0)
      = (((Ico (2 ^ M) (2 ^ (M + 1))).filter
          (fun n => Nat.Prime n ∧ Nat.Prime (n + 2))).card : ℝ) / 2 ^ M := by
    rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const]
    simp [nsmul_eq_mul, div_eq_mul_inv]
  have h3 : ((Ico (2 ^ M) (2 ^ (M + 1))).filter
      (fun n => Nat.Prime n ∧ Nat.Prime (n + 2))).card ≤ twinCount (2 ^ (M + 1)) := by
    rw [twinCount]
    refine Finset.card_le_card (fun n hn => ?_)
    simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_range] at hn ⊢
    exact ⟨hn.1.2, hn.2⟩
  have h4 : (((Ico (2 ^ M) (2 ^ (M + 1))).filter
      (fun n => Nat.Prime n ∧ Nat.Prime (n + 2))).card : ℝ) ≤ (twinCount (2 ^ (M + 1)) : ℝ) := by
    exact_mod_cast h3
  calc ∑ n ∈ Ico (2 ^ M) (2 ^ (M + 1)), twinIndicator n ≤ _ := h1
    _ = _ := h2
    _ ≤ (twinCount (2 ^ (M + 1)) : ℝ) / 2 ^ M := by gcongr

