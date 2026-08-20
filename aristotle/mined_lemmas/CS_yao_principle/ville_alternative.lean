/-
# Yao Principle
Category: Frontier Cs
Target: CS.yao_principle
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

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

set_option grind.warning false

/-!
## Overview

Mathlib has no minimax theorem, so the result is proved from scratch.  The only nontrivial
input from Mathlib is the separation theorem `geometric_hahn_banach_compact_closed`
(`Mathlib/Analysis/LocallyConvex/Separation.lean`), which is used to prove Ville's theorem of
the alternative (`CS.ville_alternative`).  Yao's principle then follows by applying the
alternative to the shifted cost matrix `cost a x - v`, where `v` is the randomized complexity,
together with weak duality (`CS.distCost_le_randCost`).
-/

namespace CS

section Orthant

variable {A : Type*}

/-- The nonnegative orthant in `A → ℝ` is convex. -/

theorem ville_alternative [Nonempty X] (M : A → X → ℝ) :
    (∃ p ∈ stdSimplex ℝ A, ∀ x, ∑ a, p a * M a x < 0) ∨
      (∃ q ∈ stdSimplex ℝ X, ∀ a, 0 ≤ ∑ x, q x * M a x) := by
  by_cases h : ∃ q ∈ stdSimplex ℝ X, ∀ a, 0 ≤ ∑ x, q x * M a x
  · exact Or.inr h
  left
  push_neg at h
  set K : Set (A → ℝ) := payoffMap M '' stdSimplex ℝ X
  set T : Set (A → ℝ) := {y : A → ℝ | ∀ a, 0 ≤ y a}
  have hKconv : Convex ℝ K := (convex_stdSimplex ℝ X).linear_image _
  have hKcomp : IsCompact K := by
    refine (isCompact_stdSimplex X).image ?_
    apply continuous_pi
    intro a
    exact continuous_finset_sum _ fun x _ => (continuous_apply x).mul continuous_const
  have hdisj : Disjoint K T := by
    rw [Set.disjoint_left]
    rintro y ⟨q, hq, rfl⟩ hyT
    obtain ⟨a, ha⟩ := h q hq
    exact absurd (hyT a) (not_le.2 ha)
  obtain ⟨f, u, v, hfK, huv, hfT⟩ :=
    geometric_hahn_banach_compact_closed hKconv hKcomp convex_nonneg_orthant
      isClosed_nonneg_orthant hdisj
  -- `v < f 0 = 0`
  have hv0 : v < 0 := by
    have := hfT 0 (by intro a; simp)
    simpa using this
  have hu0 : u < 0 := lt_trans huv hv0
  -- coefficients of `f`
  set c : A → ℝ := fun a => f (fun j => if a = j then (1 : ℝ) else 0) with hc
  have hfy : ∀ y : A → ℝ, f y = ∑ a, y a * c a := by
    intro y
    have := LinearMap.pi_apply_eq_sum_univ (f : (A → ℝ) →ₗ[ℝ] ℝ) y
    simpa [hc, smul_eq_mul] using this
  have hcnonneg : ∀ a, 0 ≤ c a := by
    intro a
    by_contra hneg
    push_neg at hneg
    set t : ℝ := v / c a with ht
    have htpos : 0 < t := div_pos_of_neg_of_neg hv0 hneg
    have hmem : (t • fun j => if a = j then (1 : ℝ) else 0) ∈ T := by
      intro b
      by_cases hb : a = b <;> simp [hb, htpos.le]
    have := hfT _ hmem
    rw [map_smul] at this
    simp only [smul_eq_mul] at this
    rw [ht, div_mul_cancel₀ _ (ne_of_lt hneg)] at this
    exact lt_irrefl v this
  have hKne : K.Nonempty := by
    obtain ⟨q, hq⟩ : (stdSimplex ℝ X).Nonempty := Set.Nonempty.of_subtype
    exact ⟨payoffMap M q, q, hq, rfl⟩
  have hSpos : 0 < ∑ a, c a := by
    rcases lt_or_eq_of_le (Finset.sum_nonneg fun a _ => hcnonneg a) with hlt | heq
    · exact hlt
    · exfalso
      have hallzero : ∀ a, c a = 0 := by
        intro a
        have := (Finset.sum_eq_zero_iff_of_nonneg (fun a _ => hcnonneg a)).1 heq.symm
        exact this a (Finset.mem_univ a)
      obtain ⟨y, hy⟩ := hKne
      have hzero : f y = 0 := by rw [hfy y]; simp [hallzero]
      have hylt := hfK y hy
      rw [hzero] at hylt
      exact absurd hylt (not_lt.2 hu0.le)
  refine ⟨fun a => c a / (∑ a', c a'), ⟨fun a => div_nonneg (hcnonneg a) hSpos.le, ?_⟩, ?_⟩
  · rw [← Finset.sum_div, div_self (ne_of_gt hSpos)]
  · intro x
    have hq : (fun x' => if x' = x then (1 : ℝ) else 0) ∈ stdSimplex ℝ X :=
      ⟨fun x' => by positivity, by simp⟩
    have hmem : payoffMap M (fun x' => if x' = x then (1 : ℝ) else 0) ∈ K :=
      Set.mem_image_of_mem _ hq
    have hlt := hfK _ hmem
    have hval : f (payoffMap M (fun x' => if x' = x then (1 : ℝ) else 0)) = ∑ a, c a * M a x := by
      rw [hfy]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [payoffMap_apply]
      simp [Finset.sum_ite_eq', mul_comm]
    rw [hval] at hlt
    have hneg : ∑ a, c a * M a x < 0 := lt_trans hlt hu0
    have : ∑ a, c a / (∑ a', c a') * M a x = (∑ a, c a * M a x) / (∑ a', c a') := by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun a _ => by ring
    rw [this]
    exact div_neg_of_neg_of_pos hneg hSpos

end Alternative

section Yao

variable {A X : Type*} [Fintype A] [Fintype X] [Nonempty A] [Nonempty X]

