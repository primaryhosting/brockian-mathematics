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

lemma abs_dvdCount_sub_le (N : ℕ) (S : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p ∧ p ≠ 2) :
    |(dvdCount N S : ℝ) - 2 ^ S.card * (N : ℝ) / (∏ p ∈ S, (p : ℝ))| ≤ 2 ^ S.card := by
  have hfib : dvdCount N S
      = ∑ T ∈ S.powerset, (((range N).filter (fun n => ∀ p ∈ S, p ∣ n * (n + 2))).filter
          (fun n => S.filter (fun p => p ∣ n) = T)).card :=
    Finset.card_eq_sum_card_fiberwise
      (fun n _ => Finset.mem_powerset.mpr (Finset.filter_subset _ _))
  have hprodpos : (0 : ℝ) < ∏ p ∈ S, (p : ℝ) := by
    refine Finset.prod_pos (fun p hp => ?_)
    exact_mod_cast (hS p hp).1.pos
  have key : ∀ T ∈ S.powerset,
      |(((((range N).filter (fun n => ∀ p ∈ S, p ∣ n * (n + 2))).filter
          (fun n => S.filter (fun p => p ∣ n) = T)).card : ℕ) : ℝ)
        - (N : ℝ) / (∏ p ∈ S, (p : ℝ))| ≤ 1 := by
    intro T hT
    have hTS : T ⊆ S := Finset.mem_powerset.mp hT
    rw [dvdCount_fiber_eq N S hS hTS]
    set a := ∏ p ∈ T, p with ha
    set b := ∏ p ∈ S \ T, p with hb
    have hapos : 0 < a := Finset.prod_pos (fun p hp => (hS p (hTS hp)).1.pos)
    have hbpos : 0 < b := Finset.prod_pos (fun p hp => (hS p (Finset.mem_sdiff.mp hp).1).1.pos)
    have hab : Nat.Coprime a b := by
      refine Nat.Coprime.prod_left (fun p hp => Nat.Coprime.prod_right (fun q hq => ?_))
      obtain ⟨hqS, hqT⟩ := Finset.mem_sdiff.mp hq
      have hpne : p ≠ q := by rintro rfl; exact hqT hp
      exact (Nat.coprime_primes (hS p (hTS hp)).1 (hS q hqS).1).mpr hpne
    have hmul : (a : ℝ) * (b : ℝ) = ∏ p ∈ S, (p : ℝ) := by
      have hba : b * a = ∏ p ∈ S, p := Finset.prod_sdiff hTS
      have h2 : a * b = ∏ p ∈ S, p := by rw [← hba]; ring
      calc (a : ℝ) * (b : ℝ) = ((a * b : ℕ) : ℝ) := by push_cast; ring
        _ = ((∏ p ∈ S, p : ℕ) : ℝ) := by rw [h2]
        _ = ∏ p ∈ S, (p : ℝ) := by push_cast; ring
    have hpair := abs_card_filter_pair_sub_le N a b hapos hbpos hab
    rw [hmul] at hpair
    exact hpair
  have hmain := abs_sum_sub_card_mul_le S.powerset
    (fun T => ((((range N).filter (fun n => ∀ p ∈ S, p ∣ n * (n + 2))).filter
      (fun n => S.filter (fun p => p ∣ n) = T)).card : ℝ))
    ((N : ℝ) / (∏ p ∈ S, (p : ℝ))) key
  rw [Finset.card_powerset] at hmain
  have hcast : ((dvdCount N S : ℕ) : ℝ)
      = ∑ T ∈ S.powerset, ((((range N).filter (fun n => ∀ p ∈ S, p ∣ n * (n + 2))).filter
          (fun n => S.filter (fun p => p ∣ n) = T)).card : ℝ) := by
    rw [hfib]; push_cast; ring
  rw [hcast]
  have : (2 : ℝ) ^ S.card * (N : ℝ) / (∏ p ∈ S, (p : ℝ))
      = ((2 ^ S.card : ℕ) : ℝ) * ((N : ℝ) / (∏ p ∈ S, (p : ℝ))) := by
    push_cast; ring
  rw [this]
  simpa using hmain

end Brun

import RequestProject.Brun.Defs

/-!
# Elementary estimates for sums and products over primes

* `Brun.prod_primesBelow_one_sub_inv_le` : `∏_{p ≤ z} (1 - 1/p) ≤ e / log z`, proved from the
  Euler product over smooth numbers.
* `Brun.sum_inv_primesBelow_pow_two_le` : `∑_{p ≤ 2^q} 1/p ≤ 5 + 4 log q`, proved from the
  bound `∏_{p ≤ n} p ≤ 4 ^ n` on the primorial.
-/

namespace Brun

open Finset

/-! ### The Euler product bound -/

/-- The completely multiplicative function `n ↦ n ^ (-s)`. -/
