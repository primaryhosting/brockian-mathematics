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

lemma siftCount_le_bonferroni (N z k : ℕ) (hk : Even k) :
    (siftCount N z : ℝ)
      ≤ ∑ j ∈ range (k + 1), (-1 : ℝ) ^ j *
          ∑ S ∈ (oddPrimesLe z).powersetCard j, (dvdCount N S : ℝ) := by
  have hcard : (siftCount N z : ℝ)
      = ∑ n ∈ range N, (if ∀ p ∈ oddPrimesLe z, ¬ p ∣ n * (n + 2) then (1 : ℝ) else 0) := by
    rw [siftCount, Finset.card_filter]
    push_cast
    rfl
  rw [hcard]
  have hstep : ∀ n ∈ range N,
      (if ∀ p ∈ oddPrimesLe z, ¬ p ∣ n * (n + 2) then (1 : ℝ) else 0)
        ≤ ∑ j ∈ range (k + 1), (-1 : ℝ) ^ j *
            (((oddPrimesLe z).powersetCard j).filter
              (fun S => ∀ p ∈ S, p ∣ n * (n + 2))).card := by
    intro n _
    exact bonferroni_sets (oddPrimesLe z) (fun p => p ∣ n * (n + 2)) k hk
  refine le_trans (Finset.sum_le_sum hstep) ?_
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum (fun j _ => ?_)
  rw [← Finset.mul_sum]
  refine le_of_eq ?_
  congr 1
  -- double counting
  have hdc : ∀ n : ℕ, ((((oddPrimesLe z).powersetCard j).filter
        (fun S => ∀ p ∈ S, p ∣ n * (n + 2))).card : ℝ)
      = ∑ S ∈ (oddPrimesLe z).powersetCard j,
          (if (∀ p ∈ S, p ∣ n * (n + 2)) then (1 : ℝ) else 0) := by
    intro n
    rw [Finset.card_filter]
    push_cast
    rfl
  simp only [hdc]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun S _ => ?_)
  rw [dvdCount, Finset.card_filter]
  push_cast
  rfl

/-- The main sieve estimate. -/
